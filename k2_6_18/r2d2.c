/*
 * R2D2 Linux Kernel Module
 */

#include <linux/skbuff.h>
#include <linux/netfilter.h>
#include <linux/netfilter_ipv4.h>
#include <linux/ip.h>
#include <linux/tcp.h>
#include <linux/ktime.h>
#include <net/ip.h>
#include <net/tcp.h>
#include <net/dst.h>
#include <linux/hash.h>
#include <linux/crc16.h>
#include <linux/completion.h>

MODULE_AUTHOR("Berk Atikoglu <atikoglu@stanford.edu>");
MODULE_DESCRIPTION("R2D2 Fast TCP Retransmission");
MODULE_LICENSE("GPL");
MODULE_VERSION("0.1b");

/*
 * Linux 2.6.20 functions
 */

static inline struct iphdr *ip_hdr(const struct sk_buff *skb)
{
  return skb->nh.iph;
}

static inline struct tcphdr *tcp_hdr(const struct sk_buff *skb)
{
  return skb->h.th;
}

static ktime_t ktime_get(void)
{
  struct timespec now;
  
  ktime_get_ts(&now);
  
  return timespec_to_ktime(now);
}

void l25_set_normalized_timespec(struct timespec *ts, time_t sec, long nsec)
{
	while (nsec >= NSEC_PER_SEC) {
		nsec -= NSEC_PER_SEC;
		++sec;
	}
	while (nsec < 0) {
		nsec += NSEC_PER_SEC;
		--sec;
	}
	ts->tv_sec = sec;
	ts->tv_nsec = nsec;
}

struct timespec l25_ns_to_timespec(const s64 nsec)
{
  struct timespec ts;
  
  if (!nsec)
    return (struct timespec) {0, 0};
  
  ts.tv_sec = div_long_long_rem_signed(nsec, NSEC_PER_SEC, &ts.tv_nsec);
  if (unlikely(nsec < 0))
    l25_set_normalized_timespec(&ts, ts.tv_sec, ts.tv_nsec);
  
  return ts;
}

struct timeval l25_ns_to_timeval(const s64 nsec)
{
  struct timespec ts = l25_ns_to_timespec(nsec);
  struct timeval tv;
  
  tv.tv_sec = ts.tv_sec;
  tv.tv_usec = (suseconds_t) ts.tv_nsec / 1000;
  
  return tv;
}

static inline s64 ktime_to_us(const ktime_t kt)
{
  struct timeval tv = l25_ns_to_timeval(kt.tv64);
  return (s64) tv.tv_sec * USEC_PER_SEC + tv.tv_usec;
}

/* 2^31 + 2^29 - 2^25 + 2^22 - 2^19 - 2^16 + 1 */
#define GOLDEN_RATIO_PRIME_32 0x9e370001UL

static inline u32 hash_32(u32 val, unsigned int bits)
{
  /* On some cpus multiply is faster, on others gcc will do shifts */
  u32 hash = val * GOLDEN_RATIO_PRIME_32;
  
  /* High bits are more random, so use them. */
  return hash >> (32 - bits);
}



#define MODULE_NAME "R2D2"
#define R2D2_VERSION "0.91"

#define GET_STATISTICS

#define THREAD_IN_ENTRY_COUNT 1000
#define THREAD_OUT_ENTRY_COUNT 1000
#define THREAD_ENTRY_COUNT 2000

#define THREAD_TIMEOUT 1

#define L25_IPV4_DS 0x80

// hash table
#define HASH_TABLE_BITS 15
#define HASH_TABLE_SIZE (1 << HASH_TABLE_BITS)

// overflow hash table
#define OHASH_TABLE_BITS 11
#define OHASH_TABLE_SIZE (1 << OHASH_TABLE_BITS)

#define OSHIFT 4

#define MAX_ENTRIES 2 * HASH_TABLE_SIZE
#define TX_TIMEOUT 3 /* ms */
#define MAX_RETRANSMIT 3 /* Maxs number of packets that a packet can be retransmitted */

#define MAX_RETRANSMIT_AT_A_TIME 100 /* Max number of packets that can retransmitted in a timeout */

#define INIT_SA 0 /* Initial SRTT Unit: us */
#define INIT_SV 10000 /* Initial RTT VAR. Unit: us */

#define MIN_RTO 3000
#define MAX_RTO 10000

#define PKTS_WAITING 0
#define PKTS_PROCESSING 1

/*
 * R2D2 Key fields:
 * IP Destination Address
 * TCP Source Port
 * TCP Desination Port
 * TCP Sequence Number
 */
typedef struct pkt_id_s {
  __be32 daddr;
  __be16 sport;
  __be16 dport;
  __be32 seq;
} pkt_id;

struct tcp_tuple {
  __be32 saddr;
  __be32 daddr;
  __be16 sport;
  __be16 dport;
};

// linked list for R2D2 packets on-the-fly
typedef struct protected_pkt_s {
  struct list_head list;
  struct pkt_hash_s *h_entry; // corresponding hash map entry
  ktime_t tstamp;  // departure time of the packet
  struct sk_buff *skb; // clone of the packet
  unsigned long jif_time; // depature time in jiffies
  int transmit_count; // number of times packets retransmitted
  struct tcp_flow_entry_s *tcp_entry;
  struct tcp_tuple tuple;
  __be32 ack_seq;
  __be32 tcp_seq;
} protected_pkt;

// linked list for R2D2 thread processing queue
typedef struct captured_pkt_s {
  struct list_head list;
  struct sk_buff *skb;
  ktime_t tstamp;
} captured_pkt;

// hash table mapping to the linked list
typedef struct pkt_hash_s {
  u8 in_use;
  pkt_id key;
  protected_pkt *data;
} pkt_hash;

struct per_cpu_var {
  struct list_head free_pkts;
  struct list_head out_pkts[2];
  struct list_head in_pkts[2];
  spinlock_t pkt_lock;
};

DEFINE_PER_CPU(struct per_cpu_var, pcvar);

static struct completion wakeup_l25_thread;
static struct completion terminate_l25_module;
static wait_queue_head_t l25_thread_event;

static pkt_hash hash_table1[HASH_TABLE_SIZE];
static pkt_hash hash_table2[HASH_TABLE_SIZE];

static pkt_hash ohash_table1[OHASH_TABLE_SIZE];
static pkt_hash ohash_table2[OHASH_TABLE_SIZE];

// tcp flow hash table
#define TCP_FLOW_HASH_TABLE_BITS 16
#define TCP_FLOW_HASH_TABLE_SIZE (1 << TCP_FLOW_HASH_TABLE_BITS)
#define TCP_FLOW_HASH_TABLE_DEPTH 4

typedef struct tcp_flow_entry_s {
  int in_use;
  struct tcp_tuple tuple;
  __be32 last_ack_received;
  __be32 last_seq_sent;
  int backoff;
  ktime_t last_pkt_sent;
  int iter_max_rtt;
  int active_pkts;

  //int why;

  s64 rto; // msec
  s64 sa;
  s64 sv;
} tcp_flow_entry;

static tcp_flow_entry tcp_flow_hash_table[TCP_FLOW_HASH_TABLE_SIZE][TCP_FLOW_HASH_TABLE_DEPTH];

static tcp_flow_entry *updated_flows[1000];
static int updated_flow_count;

static s64 flows_created;

#ifdef GET_STATISTICS

#define L25_STATS_PROC_NAME "r2d2_stats"
struct proc_dir_entry *l25_stats_proc;

#define COUNTER_COUNT 10
enum counter_var {
  PKTS_SENT,
  PKTS_HASHED_1,
  PKTS_HASHED_2,
  PKTS_HASHED_O1,
  PKTS_HASHED_O2,
  PKTS_CONFLICT,
  HASH_ENTRY_NA,
  MEMORY_NA,
  TCP_NAKED_ACK,
  PKTS_RETRANS
};

static char *counter_name[] = {
  "Packets sent",
  "Packets hashed into Table 1",
  "Packets hashed into Table 2",
  "Packets hashed into O. Table 1",
  "Packets hashed into O. Table 2",
  "Packets in conflict",
  "Hash table entry N/A",
  "Memory N/A",
  "TCP Naked ACKs",
  "Packets retransmitted"
};

s64 counter_val[COUNTER_COUNT] = { 0 };

#ifdef GET_STATISTICS
#define INCR_EVENT(type) counter_val[type]++;
#else
#define INCR_EVENT(type)
#endif

// stats
static uint acksReceived; // number of R2D2 acks received by sender
static uint ackPacketsReceived; // number of R2D2 ACK packets received
static uint unmatchedAcksReceived; // number of R2D2 ACKs that doesn't have a match in the hash table

// RTT in us
static s64 minRTT;
static s64 maxRTT;
static s64 avgRTT;
static uint numRTT;

static s64 minSRTT;
static s64 maxSRTT;
static s64 avgSRTT;
static uint numSRTT;

static s64 minVAR;
static s64 maxVAR;
static s64 avgVAR;

static uint max_retransmit_duration; // maximum wait time of a packet before retransmission
static int retransmit_count[MAX_RETRANSMIT]; // number of R2D2 retransmissions
static int packets_terminated; // number of packets discarded before without receiving a R2D2 ACK
static uint max_resend; // maximum number of packets retransmitted in a timeout
static uint max_thread_sleep; // maximum duration between two iterations
static ktime_t thread_sleep_start;

// number of  process by thread in an iteration
static uint avg_in_queue_size;
static uint max_in_queue_size;
static uint min_in_queue_size;

static uint avg_out_queue_size;
static uint max_out_queue_size;
static uint min_out_queue_size;

static uint avg_thread;
static uint min_thread;
static uint max_thread;

static uint avg_thread_in;
static uint min_thread_in;
static uint max_thread_in;

static uint avg_thread_out;
static uint min_thread_out;
static uint max_thread_out;

static uint num_thread_iter;
#endif

static struct timer_list thread_timer;

static protected_pkt out_buf;
static protected_pkt free_buf;

static char *l25_subnet;
module_param(l25_subnet, charp, 0);
static int mask;
module_param(mask, int, 0);
uint32_t subnet_addr;
uint32_t subnet_mask;

static char *iface;
module_param(iface, charp, 0);

static uint l25_terminating;
static uint notify_thread;

static int check_subnet_in(const struct net_device *dev, struct iphdr *iph);
static int check_subnet_out(const struct net_device *dev, struct iphdr *iph);
static int check_iphdr(const struct net_device *dev, struct iphdr *iph);
static int check_iface(const struct net_device *dev, struct iphdr *iph);
static int (*protect_incoming_pkt)(const struct net_device *dev, struct iphdr *iph);
static int (*protect_outgoing_pkt)(const struct net_device *dev, struct iphdr *iph);

static inline void retransmit_expired_pkts(void);

/* This is the structure we shall use to register our function */
static struct nf_hook_ops hook_in;
static struct nf_hook_ops hook_out;

static void process_tcp_ack(pkt_id *key, ktime_t tstamp, long *max_rtt, struct iphdr *iph);



void r2d2_processing_thread(unsigned long data);
static void process_incoming_pkt(captured_pkt *cpkt, long *max_rtt);
static void process_outgoing_pkt(captured_pkt *cpkt);

static inline u32 hash_func1(pkt_id *key) {
  u32 ret = crc16(0, (u8*) key, 12);
  ret = ret >> 1;
  return ret;
}

static inline u32 tcp_flow_hash_func(struct tcp_tuple *tuple) {
  u32 ret = crc16(0, (u8*) tuple, sizeof(struct tcp_tuple));
  ret = ret >> (16 - TCP_FLOW_HASH_TABLE_BITS);
  return ret;
}

static inline void delete_packet(protected_pkt *entry) {
  kfree_skb(entry->skb);
  entry->h_entry->in_use = 0;
  entry->tcp_entry->active_pkts--;

  if (entry->transmit_count > 0) {
    if (entry->transmit_count < MAX_RETRANSMIT) {
      retransmit_count[entry->transmit_count - 1]++;
    }
#ifdef GET_STATISTICS
    else {
      packets_terminated++;
    }
#endif
  }
}

static inline void printip(uint32_t ip) {
  uint32_t d[4];
  int i;

  ip = ntohl(ip);
  for (i = 0; i < 4; i++) {
    d[i] = ip & 255;
    ip = ip >> 8;
  }  
  printk(KERN_ALERT "ip: %u.%u.%u.%u\n", d[3], d[2], d[1], d[0]);
}

static inline tcp_flow_entry *get_tcp_flow_entry(struct tcp_tuple *tuple) {
  u32 tcp_flow_hash = tcp_flow_hash_func(tuple);
  tcp_flow_entry *tcp_entry = NULL;
  int i;

  for (i = 0; i < TCP_FLOW_HASH_TABLE_DEPTH; i++) {
    if (tcp_flow_hash_table[tcp_flow_hash][i].in_use == 1 && memcmp(tuple, &(tcp_flow_hash_table[tcp_flow_hash][i].tuple), 12) == 0) {
      tcp_entry = &tcp_flow_hash_table[tcp_flow_hash][i];
      break;
    }
  }

  if (tcp_entry == NULL) {
    int e_index = -1;
    for (i = 0; i < TCP_FLOW_HASH_TABLE_DEPTH; i++) {
      if (tcp_flow_hash_table[tcp_flow_hash][i].in_use == 0 || tcp_flow_hash_table[tcp_flow_hash][i].active_pkts == 0) {
	e_index = i;
	break;
      }
    }

    if (e_index == -1) {
      return NULL;
    }
#ifdef GET_STATISTICS
    flows_created++;
#endif
    tcp_entry = &tcp_flow_hash_table[tcp_flow_hash][e_index];
    tcp_entry->in_use = 1;
    tcp_entry->tuple = *tuple;
    tcp_entry->last_ack_received = 0;
    tcp_entry->backoff = 1;
    tcp_entry->last_seq_sent = 0;
    tcp_entry->iter_max_rtt = -1;
    tcp_entry->active_pkts = 0;
    tcp_entry->sa = INIT_SA;
    tcp_entry->sv = INIT_SV;
    //tcp_entry->why = 0;

    tcp_entry->rto = (tcp_entry->sa >> 3) / 1000;

    //printip(tuple->daddr);
  }

  return tcp_entry;
}

/*
 * This function is called for each incoming packet
 */
unsigned int capture_incoming_pkt(unsigned int hooknum,
			 struct sk_buff **skb_in,
			 const struct net_device *in,
			 const struct net_device *out,
			 int (*okfn)(struct sk_buff *))
{
  struct iphdr *iph;
  captured_pkt *pkt;
  struct list_head *p;
  struct tcphdr *tcph;

  struct sk_buff *skb = *skb_in;

  iph = ip_hdr(skb);

  if (protect_incoming_pkt(in ,iph)) {
    // Packet comes from a protected node
    struct per_cpu_var *pcv = &get_cpu_var(pcvar);
    spin_lock_bh(&pcv->pkt_lock);

    if (list_empty(&pcv->free_pkts)) {
      spin_unlock_bh(&pcv->pkt_lock);
      put_cpu_var(pcvar);
      return NF_ACCEPT;
    }

    tcph = (struct tcphdr *)((uint8_t *) tcp_hdr(skb) + (iph->ihl << 2));

    // clone the incoming skb
    p = pcv->free_pkts.next;
    pkt = list_entry(p, captured_pkt, list);
    pkt->skb = skb_clone(skb, GFP_ATOMIC);
    // get timestamp inline
    pkt->tstamp = ktime_get();
    if (likely(pkt->skb != NULL)) {
      list_move_tail(p, &pcv->in_pkts[PKTS_WAITING]);
    }
    else {
      INCR_EVENT(MEMORY_NA);
    }
    spin_unlock_bh(&pcv->pkt_lock);
    put_cpu_var(pcvar);
  }
  return NF_ACCEPT;
}

/*
 * This function is called for each outgoing packet
 */
unsigned int capture_outgoing_pkt(unsigned int hooknum,
			  struct sk_buff **skb_in,
			  const struct net_device *in,
			  const struct net_device *out,
			  int (*okfn)(struct sk_buff *))
{
  struct sk_buff *skb = *skb_in;
  struct iphdr *iph;
  iph = ip_hdr(skb);

  if (protect_outgoing_pkt(out, iph)) {
    captured_pkt *pkt;
    struct list_head *p;
    struct tcphdr *tcph = tcp_hdr(skb);

    uint totlen = ntohs(iph->tot_len) >> 2;

    // do not protect naked TCP ACKs
    if (totlen - iph->ihl > tcph->doff || tcph->fin || tcph->syn) {
      struct per_cpu_var *pcv = &get_cpu_var(pcvar);
      spin_lock_bh(&pcv->pkt_lock);

      if (list_empty(&pcv->free_pkts)) {
	spin_unlock_bh(&pcv->pkt_lock);
	put_cpu_var(pcvar);
	return NF_ACCEPT;
      }

      // clone outgoing skb
      p = pcv->free_pkts.next;
      pkt = list_entry(p, captured_pkt, list);
      pkt->skb = skb_clone(skb, GFP_ATOMIC);
      // get timestamp inline
      pkt->tstamp = ktime_get();
      if (likely(pkt->skb != NULL)) {
	list_move_tail(p, &pcv->out_pkts[PKTS_WAITING]);
      }
      else {
	INCR_EVENT(MEMORY_NA);
      }
      spin_unlock_bh(&pcv->pkt_lock);
      put_cpu_var(pcvar);
    }
    else {
      INCR_EVENT(TCP_NAKED_ACK);
    }
  }
  return NF_ACCEPT;
}

static inline int compare_seq(__be32 seq1, __be32 seq2) {
  return (seq1 > seq2 || seq1 < (seq2 >> 1));
}

/*
 * This function is called when R2D2 retransmission timer expires
 */
static inline void retransmit_expired_pkts(void) {
  struct list_head *p;
  protected_pkt *ppkt;
  int numResend = 0;

  // retransmit the packets that are expired
  while(!list_empty(&out_buf.list) && numResend < MAX_RETRANSMIT_AT_A_TIME) {
    int tdiff;
    p = out_buf.list.next;
    ppkt = list_entry(p, protected_pkt, list);

    if (ppkt->jif_time + TX_TIMEOUT <= jiffies) {
      struct sk_buff *send_skb;
#ifdef GET_STATISTICS
      if (jiffies - ppkt->jif_time > max_retransmit_duration) {
	max_retransmit_duration = jiffies - ppkt->jif_time;
      }
#endif

      // check if packet is ACKed
      tdiff = ktime_to_us(ktime_sub(ktime_get(), ppkt->tcp_entry->last_pkt_sent)) / 1000;
      if (compare_seq(ppkt->tcp_entry->last_ack_received, ppkt->ack_seq)) {
        //printk(KERN_ALERT "al!!!! %u, %u\n", ppkt->tcp_entry->last_ack_received, ppkt->ack_seq);
	list_move(p, &free_buf.list);
	delete_packet(ppkt);
#ifdef GET_STATISTICS
	acksReceived++;
#endif
	continue;
      }

      send_skb = ppkt->skb;

      if (ppkt->transmit_count <= MAX_RETRANSMIT) {
	if ((tdiff >= ppkt->tcp_entry->backoff * ppkt->tcp_entry->rto && ppkt->tcp_seq == ppkt->tcp_entry->last_ack_received)) {
//	  struct dst_entry *dst = skb_dst(send_skb);
	  numResend++;
	  INCR_EVENT(PKTS_RETRANS);
	  ppkt->transmit_count++;
	  ppkt->tcp_entry->backoff <<= 1;
	  ppkt->skb = skb_clone(send_skb, GFP_ATOMIC);


          /*if (ppkt->tcp_entry->why) {
            printk(KERN_ALERT "retransmit! rto: %llu, tdiff: %u, transmit count: %u, backoff: %u\n", ppkt->tcp_entry->rto, tdiff, ppkt->transmit_count, ppkt->tcp_entry->backoff);
            printk(KERN_ALERT "pkt seq: %u, last acked: %u\n", ppkt->tcp_seq, ppkt->tcp_entry->last_ack_received);
            }*/
          //struct iphdr *iph = ip_hdr(send_skb);
          //struct tcphdr *tcph = (struct tcphdr *)((uint8_t *) tcp_hdr(send_skb) + (iph->ihl << 2));
          //printk(KERN_ALERT "retransmit! %u, active: %u, seq: %u\n", ntohl(ppkt->tuple.daddr), ppkt->tcp_entry->active_pkts, ntohl(tcph->seq));

	  if (send_skb->dst->hh)
	    neigh_hh_output(send_skb->dst->hh, send_skb);
	  else if (send_skb->dst->neighbour)
	    send_skb->dst->neighbour->output(send_skb);
	}
        /*else if (print_count < 5) {
          int usec = ktime_to_us(ktime_sub(ktime_get(), ppkt->tstamp));
          if (usec > 15000) {
            printk(KERN_ALERT "why! duration: %d, rto: %llu, tdiff: %u, transmit count: %u, backoff: %u, jiff: %lu\n", usec, ppkt->tcp_entry->rto, tdiff, ppkt->transmit_count, ppkt->tcp_entry->backoff, (jiffies - ppkt->jif_time));
            printk(KERN_ALERT "pkt seq: %u, last acked: %u\n", ppkt->tcp_seq, ppkt->tcp_entry->last_ack_received);
            print_count++;
            ppkt->tcp_entry->why = 1;
          }
          }*/

	if (likely(ppkt->skb != NULL)) {
	  ppkt->jif_time = jiffies;
	  list_del(p);

	  list_add_tail(p, &out_buf.list);
	}
	else {
	  list_move(p, &free_buf.list);
	  ppkt->h_entry->in_use = 0;
	  INCR_EVENT(MEMORY_NA);
	}
      }
      else {
     	list_move(p, &free_buf.list);
	delete_packet(ppkt);
      }
    }
    else {
      break;
    }
  }

#ifdef GET_STATISTICS
  if (numResend > max_resend)
    max_resend = numResend;
#endif

}

static inline int packet_ready(void) {
  int ret = 0;
  int i;
  for_each_possible_cpu(i) {
      struct per_cpu_var *pcv;
      pcv = &per_cpu(pcvar, i);
      if (!list_empty(&pcv->in_pkts[PKTS_WAITING]) ||
	  !list_empty(&pcv->out_pkts[PKTS_WAITING])) {
	ret = 1;
	break;
      }
  }
  return ret;
}

void process_updated_flows(void) {
  int i;
  for (i = 0; i < updated_flow_count; i++) {
    tcp_flow_entry *f = updated_flows[i];
    long m = f->iter_max_rtt;
    m -= (f->sa >> 3);
    f->sa += m;
    if (m < 0)
      m = -m;
    m -= (f->sv >> 2);
    f->sv += m;
    f->rto = (f->sa >> 3);// + sv;
    
    if (f->rto < MIN_RTO) {
      f->rto = MIN_RTO;
    }
    /*if (f->rto > MAX_RTO) {
      f->rto = MAX_RTO;
      }*/
    // convert from us to ms
    f->rto /= 1000;

#ifdef GET_STATISTICS
    if (f->sa < minSRTT)
      minSRTT = f->sa;
    else if (f->sa > maxSRTT)
      maxSRTT = f->sa;
    avgSRTT += f->sa;
    if (f->sv < minVAR)
	minVAR = f->sv;
    else if (f->sv > maxVAR)
      maxVAR = f->sv;
    avgVAR += f->sv;
    numSRTT++;
#endif

    updated_flows[i]->iter_max_rtt = -1;
  }
  updated_flow_count = 0;
}

/*
 * This function performs all the R2D2 functionality
 * It first processes outgoing packets then the incoming packets
 * Later it retransmits any packets if it is time
 */
void r2d2_processing_thread(unsigned long data) {
  int i;
  int updated = 0;

#ifdef GET_STATISTICS
  // Compute the max idle time between two iterations
  uint wait_usec = ktime_to_us(ktime_sub(ktime_get(), thread_sleep_start));
  if (wait_usec > max_thread_sleep) {
    max_thread_sleep = wait_usec;
  }
#endif

  /*
   * Continue processing as long as there are packets waiting
   */
  while(packet_ready()) {
#ifdef GET_STATISTICS
    ktime_t thread_start_time = ktime_get();
    ktime_t thread_end_time;
    s64 usec;
#endif
    long m = 0;

    struct list_head *p;
    captured_pkt *pkt;

#ifdef GET_STATISTICS
    int count = 0;
    int out_count = 0;
    int in_count = 0;
#endif

    updated = 1;

    /* move waiting pkts to processing queue */
    for_each_possible_cpu(i) {
      struct per_cpu_var *pcv;
      pcv = &per_cpu(pcvar, i);

      spin_lock_bh(&pcv->pkt_lock);
      list_splice_init(&pcv->out_pkts[PKTS_WAITING],
		       &pcv->out_pkts[PKTS_PROCESSING]);
      list_splice_init(&pcv->in_pkts[PKTS_WAITING],
		       &pcv->in_pkts[PKTS_PROCESSING]);
      spin_unlock_bh(&pcv->pkt_lock);
    }

    /* process outgoing packets */
    for_each_possible_cpu(i) {
      struct per_cpu_var *pcv;
      pcv = &per_cpu(pcvar, i);
      list_for_each(p, &pcv->out_pkts[PKTS_PROCESSING]) {
	pkt = list_entry(p, captured_pkt, list);
	process_outgoing_pkt(pkt);
      }
    }

    /* process incoming packets */
    for_each_possible_cpu(i) {
      struct per_cpu_var *pcv;
      pcv = &per_cpu(pcvar, i);

      list_for_each(p, &pcv->in_pkts[PKTS_PROCESSING]) {
	pkt = list_entry(p, captured_pkt, list);
	process_incoming_pkt(pkt, &m);
	kfree_skb(pkt->skb);
      }
    }

    /* return processed entries to free pool */
    for_each_possible_cpu(i) {
      struct per_cpu_var *pcv;
      pcv = &per_cpu(pcvar, i);
      spin_lock_bh(&pcv->pkt_lock);
      while(!list_empty(&pcv->out_pkts[PKTS_PROCESSING])) {
	p = pcv->out_pkts[PKTS_PROCESSING].next;
	list_move(p, &pcv->free_pkts);
#ifdef GET_STATISTICS
	out_count++;
#endif
      }
      while(!list_empty(&pcv->in_pkts[PKTS_PROCESSING])) {
	p = pcv->in_pkts[PKTS_PROCESSING].next;
	list_move(p, &pcv->free_pkts);
#ifdef GET_STATISTICS
	in_count++;
#endif
      }
      spin_unlock_bh(&pcv->pkt_lock);
    }
#ifdef GET_STATISTICS
    if (count > max_out_queue_size)
      max_out_queue_size = count;
    if (count < min_out_queue_size)
      min_out_queue_size = count;
    avg_out_queue_size += count;
    count = 0;
#endif

#ifdef GET_STATISTICS
    if (count > max_in_queue_size)
      max_in_queue_size = count;
    if (count < min_in_queue_size)
      min_in_queue_size = count;
    avg_in_queue_size += count;
#endif

#ifdef GET_STATISTICS
    num_thread_iter++;

    thread_end_time = ktime_get();
    usec = ktime_to_us(ktime_sub(thread_end_time, thread_start_time));

    if (usec < min_thread)
      min_thread = usec;
    if (usec > max_thread)
      max_thread = usec;

    avg_thread += usec;
#endif

    retransmit_expired_pkts();
    process_updated_flows();
  }

  if (!updated) {
    // retransmit expired packets
    retransmit_expired_pkts();
    process_updated_flows();
  }

  // exit R2D2
  if (unlikely(l25_terminating)) {
    printk(KERN_INFO MODULE_NAME " - thread terminated...\n");
    complete(&terminate_l25_module);
  }
  else {

#ifdef GET_STATISTICS
    thread_sleep_start = ktime_get();
#endif
    mod_timer(&thread_timer, jiffies + THREAD_TIMEOUT);
  }
}

static inline pkt_hash *get_pkt_hash(pkt_id *pid) {
  u32 h1;
  u32 h2;
  pkt_hash *h_entry = NULL;

  // check the first hash function
  h1 = hash_func1(pid);
  if (hash_table1[h1].in_use && memcmp(pid, &hash_table1[h1].key, sizeof(pkt_id)) == 0) {
    h_entry = &hash_table1[h1];
  }
  else {
    // check the second hash function
    h2 = hash_32(h1, HASH_TABLE_BITS);

    if (hash_table2[h2].in_use && memcmp(pid, &hash_table2[h2].key, sizeof(pkt_id)) == 0) {
      h_entry = &hash_table2[h2];
    }
    // check overflow hash tables
    else {
      u16 oh1;
      u16 oh2;
      oh1 = h1 >> OSHIFT;
      if (ohash_table1[oh1].in_use && memcmp(pid, &ohash_table1[oh1].key, sizeof(pkt_id)) == 0) {
	h_entry = &ohash_table1[oh1];
      }
      else {
	oh2 = h2 >> OSHIFT;
	if (ohash_table2[oh2].in_use && memcmp(pid, &ohash_table2[oh2].key, sizeof(pkt_id)) == 0) {
	  h_entry = &ohash_table2[oh2];
	}
      }
    }
  }
  return h_entry;
}

static void process_tcp_ack(pkt_id *pid, ktime_t tstamp, long *max_rtt, struct iphdr *iph) {

  pkt_hash *h_entry;
  protected_pkt *ppkt = NULL;

  h_entry = get_pkt_hash(pid);
  
  if (h_entry) {
    s64 usec;
    ppkt = h_entry->data;
    usec = ktime_to_us(ktime_sub(tstamp, ppkt->tstamp));
    
    /*if (usec > 5000) {
      printk(KERN_ALERT "delayed! %lluus ip: %u, %u, %u\n", usec, ppkt->tuple.daddr, ppkt->tcp_seq,  ppkt->ack_seq);
      INCR_EVENT(MEMORY_NA);
      }*/
    
    if (ppkt->transmit_count == 0) {
      if (usec > *max_rtt)
	*max_rtt = usec;

#ifdef GET_STATISTICS
      if (usec < minRTT)
	minRTT = usec;
      else if (usec > maxRTT)
	maxRTT = usec;

      /*if (usec > 15000) {
        printk(KERN_ALERT "long! RTT: %llu, transmit count: %u, backoff: %u, seq: %u\n", usec, ppkt->transmit_count, ppkt->tcp_entry->backoff, ppkt->tcp_seq);
        }*/

      avgRTT += usec;
      numRTT++;
#endif

      if (ppkt->tcp_entry->iter_max_rtt == -1) {
        ppkt->tcp_entry->iter_max_rtt = usec;
        updated_flows[updated_flow_count++] = ppkt->tcp_entry;
      }
      else {
        if (ppkt->tcp_entry->iter_max_rtt < usec)
          ppkt->tcp_entry->iter_max_rtt = usec;
      }
    }

    list_move(&ppkt->list, &free_buf.list);
    delete_packet(ppkt);

  }
#ifdef GET_STATISTICS
  else {
    unmatchedAcksReceived++;
  }
#endif
}

static void process_incoming_pkt(captured_pkt *pkt, long *max_rtt) {
  struct iphdr *iph = ip_hdr(pkt->skb);
  struct tcphdr *tcph = (struct tcphdr *)((uint8_t *) tcp_hdr(pkt->skb) + (iph->ihl << 2));

  struct tcp_tuple tuple;
  tcp_flow_entry *tcp_entry = NULL;
  __be32 cum_ack;

  // do not protect local packets
  if (iph->saddr == iph->daddr) {
    return;
  }

  tuple.saddr = iph->daddr;
  tuple.daddr = iph->saddr;
  tuple.sport = tcph->dest;
  tuple.dport = tcph->source;

  tcp_entry = get_tcp_flow_entry(&tuple);

  if (!tcp_entry) {
    return;
  }

  if (unlikely(tcph->syn)) {
    tcp_entry->last_ack_received = 0;
    return;
  }

  cum_ack = ntohl(tcph->ack_seq);

  /*if (tcp_entry->why) {
    printk(KERN_ALERT "ack received: %u, last: %u", cum_ack, tcp_entry->last_ack_received);
    }*/

  if (tcph->ack && (compare_seq(cum_ack, tcp_entry->last_ack_received) || tcph->syn)) {
    pkt_id pid;

    /*if (tcp_entry->why) {
      printk(KERN_ALERT "new!\n");
      tcp_entry->why = 0;
      }*/

    tcp_entry->last_ack_received = cum_ack;
    tcp_entry->backoff = 1;

    pid.daddr = iph->saddr;
    pid.sport = tcph->dest;
    pid.dport = tcph->source;
    pid.seq = cum_ack;

    process_tcp_ack(&pid, pkt->tstamp, max_rtt, iph);

#ifdef GET_STATISTICS
    ackPacketsReceived++;
#endif
  }
  return;
}

static inline pkt_hash *get_free_hash_entry(pkt_id *pid) {
  u32 h1 = hash_func1(pid);
  u32 h2;

  // first hash table entry is available
  if (hash_table1[h1].in_use == 0) {
    INCR_EVENT(PKTS_HASHED_1);
    return &hash_table1[h1];
  }
  else {
    if (memcmp(pid, &hash_table1[h1].key, sizeof(pkt_id)) == 0) {
      hash_table1[h1].data->jif_time = jiffies;
      list_move_tail(&hash_table1[h1].data->list, &out_buf.list);
      INCR_EVENT(PKTS_CONFLICT);
      return NULL;
    }

    h2 = hash_32(h1, HASH_TABLE_BITS);
    // second hash table entry is available
    if (hash_table2[h2].in_use == 0) {
      INCR_EVENT(PKTS_HASHED_2);
      return &hash_table2[h2];
    }
    else {
      u16 oh1;
      u16 oh2;
      if (memcmp(pid, &hash_table2[h2].key, sizeof(pkt_id)) == 0) {
	INCR_EVENT(PKTS_CONFLICT);
	return NULL;
      }

      // check overflow hash table

      oh1 = h1 >> OSHIFT;
      if (ohash_table1[oh1].in_use == 0) {
        INCR_EVENT(PKTS_HASHED_O1);
	return &ohash_table1[oh1];
      }
      else {
	oh2 = h2 >> OSHIFT;
	if (ohash_table2[oh2].in_use == 0) {
          INCR_EVENT(PKTS_HASHED_O2);
	  return &ohash_table2[oh2];
	}
	else {
	  // hash tables entries are full, don't protect the packet
	  INCR_EVENT(HASH_ENTRY_NA);
	  return NULL;
	}
      }
    }
  }
  return NULL;
}

static void process_outgoing_pkt(captured_pkt *cpkt) {
  struct sk_buff *skb = cpkt->skb;
  struct iphdr *iph = ip_hdr(skb);

  protected_pkt *ppkt;
  struct list_head *p;
  struct tcphdr *tcph = tcp_hdr(skb);

  pkt_id pid;
  pkt_hash *h_entry;

  struct tcp_tuple tuple;
  tcp_flow_entry *tcp_entry = NULL;
  __be32 ack_seq;

  // do not protect local packets
  if (iph->saddr == iph->daddr) {
    kfree_skb(skb);
    return;
  }

  if (unlikely(list_empty(&free_buf.list))) {
    kfree_skb(skb);
    return;
  }

  // calculate packet id
  pid.daddr = iph->daddr;
  pid.sport = tcph->source;
  pid.dport = tcph->dest;
  pid.seq = ntohl(tcph->seq) + ntohs(iph->tot_len) - ((iph->ihl + tcph->doff) << 2);
  
  h_entry = get_free_hash_entry(&pid);
  if (!h_entry) {
    kfree_skb(skb);
    return;
  }

  h_entry->in_use = 1;
  h_entry->key = pid;

  p = free_buf.list.next;
  ppkt = list_entry(p, protected_pkt, list);

  ppkt->tstamp = cpkt->tstamp;

  h_entry->data = ppkt;
  ppkt->h_entry = h_entry;

  memcpy(&tuple, &iph->saddr, 8);
  memcpy(((u8 *)&tuple) + 8, &tcph->source, 4);

  tcp_entry = get_tcp_flow_entry(&tuple);

  // no entry available do not protect packet
  if (tcp_entry == NULL) {
    kfree_skb(skb);
    return;
  }

  INCR_EVENT(PKTS_SENT);

  tcp_entry->active_pkts++;
  ppkt->tcp_entry = tcp_entry;
  ppkt->tuple = tuple;
  tcp_entry->last_pkt_sent = cpkt->tstamp;

  // store seq and the expected the ack
  ppkt->tcp_seq = ntohl(tcph->seq);
  ack_seq = ntohs(iph->tot_len) - ((iph->ihl + tcph->doff) << 2);
  ack_seq += ppkt->tcp_seq;
  ppkt->ack_seq = ack_seq;

  if (unlikely(tcph->syn) || ack_seq > tcp_entry->last_seq_sent) {
    tcp_entry->last_seq_sent = ack_seq;
  }

  list_move_tail(p, &out_buf.list);

  ppkt->jif_time = jiffies;
  ppkt->transmit_count = 0;
  ppkt->skb = skb;

  return;
}

static int check_subnet_in(const struct net_device *dev, struct iphdr *iph) {
  return ((iph->saddr & subnet_mask) == subnet_addr && iph->protocol == IPPROTO_TCP);
}

static int check_subnet_out(const struct net_device *dev, struct iphdr *iph) {
  return ((iph->daddr & subnet_mask) == subnet_addr && iph->protocol == IPPROTO_TCP);
}

static int check_iphdr(const struct net_device *dev, struct iphdr *iph) {
  return ((iph->tos & L25_IPV4_DS) && iph->protocol == IPPROTO_TCP);
}

static int check_iface(const struct net_device *dev, struct iphdr *iph) {
  return (strcmp(dev->name, iface) == 0);
}

#ifdef GET_STATISTICS

static void *l25_stats_proc_seq_start(struct seq_file *s, loff_t *pos)
{
  static unsigned long counter = 0;
  if (*pos == 0) {
    return &counter;
  }
  else {
    *pos = 0;
    return NULL;
  }
}

/**
 * This function is called after the beginning of a sequence.
 * It's called untill the return is NULL (this ends the sequence).
 *
 */
static void *l25_stats_proc_seq_next(struct seq_file *s, void *v, loff_t *pos)
{
  unsigned long *index = (unsigned long *)v;
  (*index)++;

  return NULL;
}

/**
 * This function is called at the end of a sequence
 *
 */
static void l25_stats_proc_seq_stop(struct seq_file *s, void *v)
{

  /* nothing to do, we use a static value in start() */
}

/**
 * This function is called for each "step" of a sequence
 *
 */
static int l25_stats_proc_seq_show(struct seq_file *s, void *v)
{
  int i;
  seq_printf(s, "ACKs received: %u\n", (acksReceived + ackPacketsReceived));
  seq_printf(s, "ACK packets received: %u\n", ackPacketsReceived);
  seq_printf(s, "Unmatched ACKs received: %u\n", unmatchedAcksReceived);
  seq_printf(s, "Max retransmit duration: %u\n", max_retransmit_duration);
  seq_printf(s, "Max # of packets retransmitted in a timeout: %u\n", max_resend);
  for (i = 0 ; i < MAX_RETRANSMIT; i++)
    seq_printf(s, "Packets retransmitted %u times: %u\n", (i + 1), retransmit_count[i]);
  seq_printf(s, "Packets discarded without receiving an ACK: %u\n", packets_terminated);

  if (num_thread_iter > 0) {
    seq_printf(s, "Number of thread iterations: %u\n", num_thread_iter);
    seq_printf(s, "Outgoing queue - avg size: %u\n", (avg_out_queue_size) / num_thread_iter);
    seq_printf(s, "Outgoing queue - min size: %u\n", min_out_queue_size);
    seq_printf(s, "Outgoing queue - max size: %u\n", max_out_queue_size);
    seq_printf(s, "Incoming queue - avg size: %u\n", (avg_in_queue_size) / num_thread_iter);
    seq_printf(s, "Incoming queue - min size: %u\n", min_in_queue_size);
    seq_printf(s, "Incoming queue - max size: %u\n", max_in_queue_size);
    seq_printf(s, "Avg iteration duration: %u\n", (avg_thread / num_thread_iter));
    seq_printf(s, "Min iteration duration: %u\n", min_thread);
    seq_printf(s, "Max iteration duration: %u\n", max_thread);
    seq_printf(s, "Max iteration sleep: %u\n", max_thread_sleep);
  }

  if (numRTT > 0) {
    seq_printf(s, "Min RTT: %llu usec\n", minRTT);
    seq_printf(s, "Max RTT: %llu usec\n", maxRTT);
    seq_printf(s, "Avg RTT: %llu usec, Num RTT: %u\n", (avgRTT / numRTT), numRTT);
  }

  if (numSRTT > 0) {
    seq_printf(s, "Min SRTT: %llu usec\n", minSRTT / 8);
    seq_printf(s, "Max SRTT: %llu usec\n", maxSRTT / 8);
    seq_printf(s, "Avg SRTT: %llu usec, Num RTT: %u\n", (avgSRTT / (numSRTT * 8)), numSRTT);

    seq_printf(s, "Min VAR: %llu usec\n", minVAR / 4);
    seq_printf(s, "Max VAR: %llu usec\n", maxVAR / 4);
    seq_printf(s, "Avg VAR: %llu usec, Num RTT: %u\n", (avgVAR / (numSRTT * 4)), numSRTT);
  }

  seq_printf(s, "Flows created: %llu\n", flows_created);

  for (i = 0; i < COUNTER_COUNT; i++) {
    seq_printf(s, "%s: %llu\n", counter_name[i], counter_val[i]);
  }
  return 0;
}


static struct seq_operations l25_stats_proc_seq_ops = {
  .start = l25_stats_proc_seq_start,
  .next  = l25_stats_proc_seq_next,
  .stop  = l25_stats_proc_seq_stop,
  .show  = l25_stats_proc_seq_show
};

static int l25_stats_proc_open(struct inode *inode, struct file *file)
{
  return seq_open(file, &l25_stats_proc_seq_ops);
};

static struct file_operations l25_stats_proc_file_ops = {
  .owner   = THIS_MODULE,
  .open    = l25_stats_proc_open,
  .read    = seq_read,
  .llseek  = seq_lseek,
  .release = seq_release
};

#endif

/*
 * R2D2 module initialization function
 */
static int l25_init(void)
{
  int i;
  int ip[4];
  //print_count = 0;
  printk(KERN_ALERT "%s %s loaded...\n", MODULE_NAME, R2D2_VERSION);

  if (l25_subnet != NULL) {
    if (mask <= 0 || mask > 31) {
      printk(KERN_ERR MODULE_NAME " - mask should be in the range (0-31]\n");
      return -1;
    }

    printk(KERN_INFO MODULE_NAME " - protect subnet: %s\n", l25_subnet);
    sscanf(l25_subnet, "%d.%d.%d.%d", &ip[3], &ip[2], &ip[1], &ip[0]);
    subnet_addr = ip[3];
    subnet_addr = subnet_addr << 8;
    subnet_addr = subnet_addr | ip[2];
    subnet_addr = subnet_addr << 8;
    subnet_addr = subnet_addr | ip[1];
    subnet_addr = subnet_addr << 8;
    subnet_addr = subnet_addr | ip[0];
    subnet_addr = htonl(subnet_addr);

    subnet_mask = ((1 << mask) - 1) << (32 - mask);
    subnet_mask = htonl(subnet_mask);

    subnet_addr &= subnet_mask;

    printk(KERN_INFO "subnet addr: %u, mask: %u\n", subnet_addr, subnet_mask);

    protect_incoming_pkt = &check_subnet_in;
    protect_outgoing_pkt = &check_subnet_out;
  }
  else if (iface != NULL) {
    printk(KERN_INFO MODULE_NAME " - protect interface: %s\n", iface);
    protect_incoming_pkt = &check_iface;
    protect_outgoing_pkt = &check_iface;
  }
  else {
    printk(KERN_INFO MODULE_NAME " - protect packets according to DS\n");
    protect_incoming_pkt = &check_iphdr;
    protect_outgoing_pkt = &check_iphdr;
  }

  // initialize hash table
  for (i = 0; i < HASH_TABLE_SIZE; i++) {
    hash_table1[i].in_use = 0;
    hash_table1[i].data = NULL;

    hash_table2[i].in_use = 0;
    hash_table2[i].data = NULL;
  }

  for (i = 0; i < OHASH_TABLE_SIZE; i++) {
    ohash_table1[i].in_use = 0;
    ohash_table1[i].data = NULL;

    ohash_table2[i].in_use = 0;
    ohash_table2[i].data = NULL;
  }

  init_timer(&thread_timer);
  thread_timer.data = 0;
  thread_timer.function = r2d2_processing_thread;

  for (i = 0; i < TCP_FLOW_HASH_TABLE_SIZE; i++) {
    int j;
    for (j = 0; j < TCP_FLOW_HASH_TABLE_DEPTH; j++) {
      tcp_flow_hash_table[i][j].in_use = 0;
    }
  }

  flows_created = 0;
  updated_flow_count = 0;

#ifdef GET_STATISTICS
  l25_stats_proc = create_proc_entry(L25_STATS_PROC_NAME, 0, NULL);
  if (l25_stats_proc) {
    l25_stats_proc->proc_fops = &l25_stats_proc_file_ops;
  }

  // initialize stats
  acksReceived = 0;
  ackPacketsReceived = 0;
  unmatchedAcksReceived = 0;

  minRTT = 999999;
  maxRTT = 0;
  avgRTT = 0;
  numRTT = 0;

  minSRTT = 999999;
  maxSRTT = 0;
  avgSRTT = 0;
  numSRTT = 0;

  minVAR = 999999;
  maxVAR = 0;
  avgVAR = 0;

  packets_terminated = 0;
  for (i = 0; i < MAX_RETRANSMIT; i++) {
    retransmit_count[i] = 0;
  }
  max_retransmit_duration = 0;
  max_resend = 0;
  max_thread_sleep = 0;

  avg_out_queue_size = 0;
  max_out_queue_size = 0;
  min_out_queue_size = 999999;

  avg_in_queue_size = 0;
  max_in_queue_size = 0;
  min_in_queue_size = 999999;

  avg_thread = 0;
  max_thread = 0;
  min_thread = 9999999;

  avg_thread_in = 0;
  max_thread_in = 0;
  min_thread_in = 9999999;

  avg_thread_out = 0;
  max_thread_out = 0;
  min_thread_out = 9999999;

  num_thread_iter = 0;
#endif

  INIT_LIST_HEAD(&out_buf.list);
  INIT_LIST_HEAD(&free_buf.list);

  // initialize R2D2 structures
  l25_terminating = 0;
  notify_thread = 1;

  for_each_possible_cpu(i) {
    struct per_cpu_var *pcv;
    int j;
    pcv = &per_cpu(pcvar, i);

    spin_lock_init(&pcv->pkt_lock);
    for (j = 0; j < 2; j++) {
      INIT_LIST_HEAD(&pcv->in_pkts[j]);
      INIT_LIST_HEAD(&pcv->out_pkts[j]);
    }
    INIT_LIST_HEAD(&pcv->free_pkts);

    for (j = 0; j < THREAD_ENTRY_COUNT; j++) {
      captured_pkt *entry = kmalloc(sizeof(captured_pkt), GFP_KERNEL);
      list_add(&entry->list, &pcv->free_pkts);
    }
  }

  // initialize output buffer
  printk(KERN_INFO MODULE_NAME " - Outgoing buffer size: %u packets, %u KB\n", MAX_ENTRIES, (uint)(MAX_ENTRIES * sizeof(protected_pkt) / 1024));

  for (i = 0; i < MAX_ENTRIES; i++) {
    protected_pkt *entry = kmalloc(sizeof(protected_pkt), GFP_KERNEL);
    list_add(&entry->list, &free_buf.list);
  }

  // capute incoming packets
  hook_in.hook = capture_incoming_pkt;
  hook_in.hooknum  = NF_IP_LOCAL_IN;
  hook_in.pf       = PF_INET;
  hook_in.priority = NF_IP_PRI_FIRST;

  // capture outgoing packets
  hook_out.hook = capture_outgoing_pkt;
  hook_out.hooknum  = NF_IP_POST_ROUTING;
  hook_out.pf       = PF_INET;
  hook_out.priority = NF_IP_PRI_FIRST;

  init_completion(&wakeup_l25_thread);
  init_completion(&terminate_l25_module);
  init_waitqueue_head(&l25_thread_event);

  nf_register_hook(&hook_in);
  nf_register_hook(&hook_out);

#ifdef GET_STATISTICS
  thread_sleep_start = ktime_get();
#endif
  mod_timer(&thread_timer, jiffies + THREAD_TIMEOUT);

  return 0;
}


/*
 * R2D2 module termination function
 */
static void l25_exit(void)
{
  struct list_head *p;
  protected_pkt *cur;
  captured_pkt *cur_thread;
  int count;
  int i;

  nf_unregister_hook(&hook_in);
  nf_unregister_hook(&hook_out);

  printk(KERN_INFO MODULE_NAME " - exit...\n");

  l25_terminating = 1;
  wait_for_completion(&terminate_l25_module);

  printk(KERN_INFO MODULE_NAME " - module terminating...\n");

  count = 0;

  while(!list_empty(&out_buf.list)) {
    p = out_buf.list.next;
    list_del(p);
    cur = list_entry(p, protected_pkt, list);
    kfree(cur);
    count++;
  }
  printk(KERN_INFO MODULE_NAME " - Outstanding packets: %d\n", count);

  count = 0;
  while(!list_empty(&free_buf.list)) {
    p = free_buf.list.next;
    list_del(p);
    cur = list_entry(p, protected_pkt, list);
    kfree(cur);
    count++;
  }
  printk(KERN_INFO MODULE_NAME " - Free packets: %d\n", count);

  /* Free thread entries */
  for_each_possible_cpu(i) {
    struct per_cpu_var *pcv;
    int j;
    pcv = &per_cpu(pcvar, i);

    count = 0;
    while(!list_empty(&pcv->free_pkts)) {
      p = pcv->free_pkts.next;
      list_del(p);
      cur_thread = list_entry(p, captured_pkt, list);
      kfree(cur_thread);
      count++;
    }
    printk(KERN_INFO MODULE_NAME " - Packets deleted from free thread list: %d\n", count);

    for(j = 0; j < 2; j++) {
      while(!list_empty(&pcv->in_pkts[j])) {
	p = pcv->in_pkts[j].next;
	list_del(p);
	cur_thread = list_entry(p, captured_pkt, list);
	kfree(cur_thread);
      }

      while(!list_empty(&pcv->out_pkts[j])) {
	p = pcv->out_pkts[j].next;
	list_del(p);
	cur_thread = list_entry(p, captured_pkt, list);
	kfree(cur_thread);
      }
    }
  }

#ifdef GET_STATISTICS
  remove_proc_entry(L25_STATS_PROC_NAME, NULL);
#endif

  printk(KERN_INFO MODULE_NAME " - Flows created: %llu\n", flows_created);
}

module_init(l25_init);
module_exit(l25_exit);

EXPORT_SYMBOL(hash_func1);
EXPORT_SYMBOL(tcp_flow_hash_func);
EXPORT_SYMBOL(delete_packet);
EXPORT_SYMBOL(get_tcp_flow_entry);
EXPORT_SYMBOL(capture_incoming_pkt);
EXPORT_SYMBOL(capture_outgoing_pkt);
EXPORT_SYMBOL(retransmit_expired_pkts);
EXPORT_SYMBOL(packet_ready);
EXPORT_SYMBOL(r2d2_processing_thread);
EXPORT_SYMBOL(process_tcp_ack);
EXPORT_SYMBOL(process_incoming_pkt);
EXPORT_SYMBOL(process_outgoing_pkt);
EXPORT_SYMBOL(check_subnet_in);
EXPORT_SYMBOL(check_subnet_out);
EXPORT_SYMBOL(check_iphdr);
