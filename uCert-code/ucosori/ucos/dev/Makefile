#===============================================================================
# /* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
#===============================================================================
AR	= ar
AS	= as
AFLAGS	= -I ../boot
LD	= ld
LDFLAGS	= -s -x
CC	= gcc
CFLAGS	= -Wall -O0 -ffreestanding -fno-inline -I../include -I../
CPP	= gcc -E -nostdinc -I../include -I../

.c.s:
	$(CC) $(CFLAGS) -S -o $*.s $<
.c.o:
	$(CC) $(CFLAGS) -c -o $*.o $<
.s.o:
	$(AS) $(AFLAGS) -o $*.o $<

OBJS	= scr.o

dev.o: $(OBJS)
	$(LD) -r -o $*.o $(OBJS)
	sync

clean:
	rm -f core *.o *.a tmp_make
	for i in *.c;do rm -f `basename $$i .c`.s;done

dep:
	sed '/\#\#\# Dependencies/q' < Makefile > tmp_make
	(for i in *.c;do echo -n `echo $$i | sed 's,\.c,\.s,'`" "; \
		$(CPP) -M $$i;done) >> tmp_make
	cp tmp_make Makefile
	rm -f tmp_make

### Dependencies:
