.include "asm/asm.inc"
#===============================================================================
.globl _start
#===============================================================================
.text
.code16
#===============================================================================
_start:
	mov	$TEMP_SEG,%ax
	mov	%ax,%ds
	mov	$LOAD_SEG,%ax
	mov	%ax,%es
	mov	%es:P_LOAD_SEC,%cx
	shl	$8,%cx
	mov	$LOAD_OFF,%si
	mov	$LOAD_OFF,%di
	cld
	repz	movsw
	shr	$4,%si
	mov	%si,%es:P_KERN_OFF
	ljmp	$LOAD_SEG,$go
#===============================================================================
go:
	mov	%cs,%ax
	mov	%ax,%ds
	mov	%ax,%es
	mov	%ax,%ss
	mov	$0x8000,%sp		# arbitrary value >>512
	cli
	call	disp_load
	call	move_kernel
	call	move_gdt
	in	$0x92,%al		# enable A20
	or	$0x2,%al
	out	%al,$0x92
	mov	%cs,%ax			# set gdt & idt
	mov	%ax,%ds
	lgdt	gdt_48
	lidt	idt_48
	mov	$0x0001,%ax		# load machine status word
	lmsw	%ax
	ljmp	$SEL_CS,$0x0		# long jump to kernel
#===============================================================================
move_kernel:
	mov	P_KERN_SEC,%dx
	mov	$TEMP_SEG,%ax
	add	P_KERN_OFF,%ax
	mov	$KERNEL_BASE/0x10,%bx
	cld
do_move:
	mov	$0x80,%cx
	cmp	%cx,%dx
	jnb	move_it
	mov	%dx,%cx
move_it:
	sub	%cx,%dx
	shl	$8,%cx	
	mov	%ax,%ds
	mov	%bx,%es
	xor	%si,%si
	xor	%di,%di
	rep	movsw
	add	$0x1000,%ax
	add	$0x1000,%bx
	or	%dx,%dx
	jnz	do_move
	ret
#===============================================================================
move_gdt:
	mov	%cs,%ax
	movw	%ax,%ds
	movw	$GDT_ADDR>>4,%ax
	movw	%ax,%es
	movw	$gdt,%si
	xorw	%di,%di
	movw	$GDT_SIZE>>2,%cx
	rep	movsl
	ret
#===============================================================================
disp_load:
	mov	$msg_len,%cx
	mov	$load_msg,%bp
	call	disp_str
	ret
load_msg:
	.ascii	"\n\r\n\rLoading ..."
msg_len	= (. - load_msg)
#===============================================================================
disp_str:
	push	%cx
	mov	$0x03,%ah
	xor	%bh,%bh
	int	$0x10
	pop	%cx
	mov	$0x0007,%bx
	mov	$0x1301,%ax
	int	$0x10
	ret
#===============================================================================
# GDT
gdt:	Descriptor	0, 0, 0
	Descriptor	0, 0x0fffff, DA_CR  | DA_32 | DA_4K		# 0 ~ 4G
	Descriptor	0, 0x0fffff, DA_DRW | DA_32 | DA_4K		# 0 ~ 4G
	Descriptor	VIDEO_BASE, 0x00ffff, DA_DRW | DA_DPL3		# Video
	Descriptor	0, 0, 0
	Descriptor	0, 0, 0
gdt_48:	.word	.-gdt-1
	.long	GDT_ADDR
#===============================================================================
# IDT
idt_48:	.word	256*8-1			# idt contains 256 entries
	.long	IDT_ADDR
#===============================================================================
