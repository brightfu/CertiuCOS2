#===============================================================================
# /* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
#===============================================================================
AR	= ar
AS	= as
AFLAGS	= 
LD	= ld
LDFLAGS	= -s -x
CC	= gcc
CFLAGS	= 
CPP	= gcc -E

.c.s:
	$(CC) $(CFLAGS) \
	-S -o $*.s $<
.c.o:
	$(CC) $(CFLAGS) \
	-c -o $*.o $<
.s.o:
	$(AS) $(AFLAGS) -o $*.o $<

OBJS	= build

build: build.c
	$(CC) -o $@ $<

clean:
	rm -f core *.o *.a *.efl *.bin *.img  $(OBJS) tmp_make
	for i in *.c;do rm -f `basename $$i .c`.s;done

dep:
	sed '/\#\#\# Dependencies/q' < Makefile > tmp_make
	(for i in *.c;do echo -n `echo $$i | sed 's,\.c,\.s,'`" "; \
		$(CPP) -M $$i;done) >> tmp_make
	cp tmp_make Makefile
	rm -f tmp_make

### Dependencies:
