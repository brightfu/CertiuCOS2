#===============================================================================
# /* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
#===============================================================================
.include "asm/asm.inc"
#===============================================================================
.globl _start
.globl	os_getvect,os_setvect,inb,outb
#===============================================================================
.code32
.text
#===============================================================================
_start: 
	mov	$SEL_DS,%ax
	mov	%ax,%ds
	mov	%ax,%es
	mov	%ax,%fs
	mov	%ax,%gs
	mov	%ax,%ss
	mov	$STACK_TOP,%esp
        cli
	call	setup_idt
	call	setup_kernel
	call	init_8259A
	sti
	call	main
1:	jmp	1b
#===============================================================================
setup_idt:
	lea	dummy_int,%edx
	movl	$0x00080000,%eax
	movw	%dx,%ax			# selector = 0x0008 = cs
	movw	$0x8E00,%dx		# interrupt gate - dpl=0, present
	mov	$IDT_ADDR, %edi
	mov	$256,%ecx
1:
	movl	%eax,(%edi)
	movl	%edx,4(%edi)
	addl	$8,%edi
	dec	%ecx
	jne	1b
	ret
#===============================================================================
dummy_int:
	incb	VIDEO_BASE+640		# put something on the screen
	movb	$2,VIDEO_BASE+641	# so that we know something
	iret				# happened
#===============================================================================
# void os_setvect(int vectno, void (*isr)(void));
#===============================================================================
os_setvect: 
	pushl	%ebp
	mov	%esp,%ebp
	push	%eax
	push	%ebx
	pushfl
	cli
	mov	$IDT_ADDR,%ebx
	mov	8(%ebp),%eax		# vectno
	shl	$3,%eax
	add	%eax,%ebx
	mov	12(%ebp),%eax		# isr
	mov	%ax,(%ebx)
	shr	$16,%eax
	mov	%ax,6(%ebx)
	movw	%cs,%ax
	mov	%ax,2(%ebx)
	mov	$0x8e00,%ax		# DA_386IGate
	mov	%ax,4(%ebx)
	popfl
	pop	%ebx
	pop	%eax
	leave
	ret
#===============================================================================
# void *os_getvect(int vectno);
#===============================================================================
os_getvect: 
	push	%ebp
	mov	%esp,%ebp
	push	%ebx
	push	%ecx
	mov	$IDT_ADDR,%ebx		# Base address IDT table
	movl	8(%ebp),%eax		# vectno
	shl	$3,%eax
	add	%eax,%ebx
	xorl	%eax,%eax
	xorl	%ecx,%ecx
	mov	(%ebx),%ax		# Lower 16 bits of the handler
	mov	6(%ebx),%cx		# Higher 16 bits of the handler
	shl	$16,%ecx
	or	%ecx,%eax
	popl	%ecx
	popl	%ebx
	leave
	ret
#===============================================================================
.macro out_byte num, port
	mov	\num,%al
	out	%al,\port
	.word	0x00eb,0x00eb
.endm
#===============================================================================
init_8259A:
	out_byte	$0x11, $0x20		# Master 8259, ICW1
	out_byte	$0x11, $0xa0		# Slave  8259, ICW1
	out_byte	$0x20, $0x21		# Master 8259, ICW2
	out_byte	$0x28, $0xa1		# Slave  8259, ICW2
	out_byte	$0x04, $0x21		# Master 8259, ICW3
	out_byte	$0x02, $0xa1		# Slave  8259, ICW3
	out_byte	$0x01, $0x21		# Master 8259, ICW4.
	out_byte	$0x01, $0xa1		# Slave  8259, ICW4.
	out_byte	$0b11111100, $0x21	# Master 8259, OCW1. 
	#out_byte	$0b11111110, $0x21	# Master 8259, OCW1.
	out_byte	$0xff, $0xa1		# Slave  8259, OCW1.
	#out_byte	$0x00, $0xa1		# Slave  8259, OCW1.  
	ret
#===============================================================================
# unsigned char inb(int port);
#===============================================================================
inb: 
	push	%ebp
	mov	%esp,%ebp
	push	%dx
	mov	8(%ebp),%dx		#port
	in	%dx,%al #retval
	jmp	1f
1:	pop	%dx
	leave
	ret
#===============================================================================
# int outb(unsigned char val, int port);
#===============================================================================
outb: 
	push	%ebp
	mov	%esp,%ebp
	push	%dx
	mov	8(%ebp),%al		#val
	mov	12(%ebp),%dx		#port
	out	%al,%dx
	xor	%eax,%eax		#retval
	jmp	1f
1:	pop	%dx
	leave
	ret
#===============================================================================
