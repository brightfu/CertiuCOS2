#===============================================================================
# /* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
#===============================================================================
AR	= ar
AS	= as
AFLAGS	= -I ../include
LD	= ld
LDFLAGS	= -Ttext 0
CC	= gcc
CFLAGS	= -Wall -O0 -fno-builtin -fno-inline -I../include
CPP	= gcc -E -nostdinc -I../include
OBJCOPY	= objcopy
TFLAGS	= -R .pdr -R .comment -R.note -S -O binary
DASM	= objdump
DAFLAGS	= -D

BOOTBIN	= boot/boot.bin
LOADBIN	= boot/load.bin
BOOTOBJ	= $(BOOTBIN) $(LOADBIN)

KERNELF	= tools/kernel.bin
KERNBIN	= tools/kernel.bin
KERNIMG	= tools/kernel.img
BUILDER	= tools/build

DISKIMG	= build/Image
ASMFILE	= build/System.asm
MAPFILE	= build/System.map
FLOPPY	= build/floppy
OUTFILE	= /dev/fd1

APPOBJ	= app/app.o
ARCHOBJ	= arch/arch.o
DEVOBJ	= dev/dev.o
KERNOBJ	= ucos/kern.o
#EFSLLIB	= efs/libefsl.a
OBJS	= $(ARCHOBJ) $(KERNOBJ) $(DEVOBJ) $(APPOBJ)

#all :	message $(EFSLLIB) $(DISKIMG)
all :	$(DISKIMG)
message:
	@echo "########## Building Quminix Kerenl Image File ...... ##########"

dasm:	$(KERNELF)
	$(DASM) $(DAFLAGS) $(KERNELF) > $(ASMFILE)

$(DISKIMG): $(BOOTBIN) $(LOADBIN) $(KERNELF) $(BUILDER)
	@$(OBJCOPY) $(TFLAGS) $(KERNELF) $(KERNBIN)
	@$(BUILDER) $(BOOTBIN) $(LOADBIN) $(KERNBIN) > $(DISKIMG)
	sync
	
disk:	all
	dd if=$(DISKIMG) of=$(OUTFILE)
	
#$(KERNELF): $(OBJS)
#	$(LD) $(LDFLAGS) -L./efs -o $@ $^ -lefsl -Map $(MAPFILE)

$(KERNELF): $(OBJS)
	$(LD) $(LDFLAGS) -o $@ $^ -Map $(MAPFILE)

$(BOOTOBJ):
	(cd boot; make)

$(APPOBJ):
	(cd app; make)

$(ARCHOBJ):
	(cd arch; make)

$(DEVOBJ):
	(cd dev; make)

$(KERNOBJ):
	(cd ucos; make)

#$(EFSLLIB):
#	(cd efs; make)

$(BUILDER):
	(cd tools; make)

clean:
	@rm -f $(DISKIMG) $(ASMFILE) $(MAPFILE)
	(cd boot; make clean)
	(cd app; make clean)
	(cd arch; make clean)
	(cd dev; make clean)
	(cd ucos; make clean)
#	(cd efs; make clean)
	(cd tools; make clean)

dep:
	(cd app; make dep)
	(cd arch; make dep)
	(cd dev; make dep)
	(cd ucos; make dep)
	(cd tools; make dep)
