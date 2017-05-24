#===============================================================================
# /* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
#===============================================================================
AR	= ar
AS	= as
LD	= ld
CC	= gcc
CPP	= gcc -E

CPPFLAGS= -I../include -I../
CFLAGS	= $(CPPFLAGS) -O2 -Wall -ffreestanding -fno-builtin -nostdinc
AFLAGS	= $(CPPFLAGS) -W
LDFLAGS	= -r

.c.s:
	$(CC) $(CFLAGS) -S -o $*.s $<
.c.o:
	$(CC) $(CFLAGS) -c -o $*.o $<
.s.o:
	$(AS) $(AFLAGS) -o $*.o $<

OBJCOPY	= objcopy
TFLAGS	= -R .pdr -R .comment -R.note -S -O binary

BOOTOBJ	= boot.bin load.bin

all: $(BOOTOBJ)

boot.bin: boot.s
	$(AS) $(AFLAGS) -o boot.o boot.s
	$(LD) -s -Ttext 0x7c00 boot.o -o boot.elf
	$(OBJCOPY) $(TFLAGS) boot.elf $@
	sync

load.bin: load.s
	$(AS) $(AFLAGS) -o load.o load.s
	$(LD) -s -Ttext 0x200 load.o -o load.elf
	$(OBJCOPY) $(TFLAGS) load.elf $@
	sync

clean:
	rm -f core *.o *.bin *.elf *.a
#	for i in *.c;do rm -f `basename $$i .c`.s;done

dep:
	sed '/\#\#\# Dependencies/q' < Makefile > tmp_make
	(for i in *.c;do echo -n `echo $$i | sed 's,\.c,\.s,'`" "; \
		$(CPP) -M $$i;done) >> tmp_make
	cp tmp_make Makefile
	rm -f tmp_make

### Dependencies:
