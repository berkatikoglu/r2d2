obj-m += r2d2.o

all:
	make -C /lib/modules/2.6.18/build M=$(PWD) modules

clean:
	make -C /lib/modules/2.6.18/build M=$(PWD) clean
