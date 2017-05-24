#===============================================================================
# /* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
#===============================================================================
AR	= ar
AS	= as
AFLAGS	= 
LD	= ld
LDFLAGS	= -s -x
CC	= gcc
CFLAGS	= -Wall -O0 -ffreestanding -fno-inline -I./ -I./cpu -I./com -I../include
CPP	= gcc -E -nostdinc -I./ -I./cpu -I./com

.c.s:
	$(CC) $(CFLAGS) -S -o $*.s $<
.c.o:
	$(CC) $(CFLAGS) -c -o $*.o $<
.s.o:
	$(AS) $(AFLAGS) -o $*.o $<

CPUOBJ	= ./cpu/os_cpu_a.o ./cpu/os_cpu_c.o
UCOSOBJ	= ./com/ucos_ii.o
OBJS	= $(CPUOBJ) $(UCOSOBJ)

kern.o: $(OBJS)
	$(LD) -r -o $*.o $(OBJS)
	sync

clean:
	rm -f core *.o *.a tmp_make
	rm -f ./cpu/*.o ./com/*.o
	for i in *.c;do rm -f `basename $$i .c`.s;done

dep:
	sed '/\#\#\# Dependencies/q' < Makefile > tmp_make
	(for i in *.c;do echo -n `echo $$i | sed 's,\.c,\.s,'`" "; \
		$(CPP) -M $$i;done) >> tmp_make
	cp tmp_make Makefile
	rm -f tmp_make

### Dependencies:
