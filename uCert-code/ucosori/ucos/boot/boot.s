.include "asm/asm.inc"
#===============================================================================
.globl _start
#===============================================================================
.code16
.text
#===============================================================================
_start:
	mov	%cs,%ax
	mov	%ax,%ds
	mov	%ax,%es
	mov	%ax,%ss
	mov	$0x8000, %sp
	call	disp_boot
	call	read_kimg
	call	kill_motor
	call	copy_size
	jmp	$TEMP_SEG,$LOAD_OFF
#===============================================================================
read_kimg:				# read loader & kernel (to 0x10000)
	mov	$TEMP_SEG,%ax
	add	$LOAD_OFF/0x10,%ax
	mov	img_sec,%si
	add	img_sec+2,%si
	call	read_it
	ret
#===============================================================================
read_it:
	mov	%ax,%es
	mov	$0x0000,%bx
	mov	%bx,secnum
read_loop:
	call	setsec
	call	read_sec
	mov	secnum,%cx
	cmp	%si,%cx
	jnz	read_loop
	ret
sects:	.word 18			# 1.44Mb disks
heads:	.word 2
curcs:	.word 0x0002
curhd:	.byte 0
secnum:	.word 0
#===============================================================================
setsec:
	mov	curcs,%cx
	cmp	sects,%cl
	jbe	sret
	incb	curhd
	mov	heads,%al
	cmp	%al,curhd
	jnz	chs
	movb	$0,curhd
	inc	%ch
chs:
	mov	$1,%cl
	mov	%cx,curcs
sret:
	ret
#===============================================================================
read_sec:
	mov	$0x0201,%ax
	mov	curcs,%cx
	mov	curhd,%dh
	mov	$0,%dl
	int	$0x13
	jb	read_err
	incw	curcs
	incw	secnum
	add	$0x200,%bx
	jnc	read_ret
	mov	%es,%ax
	add	$0x1000,%ax
	mov	%ax,%es
read_ret:
	ret
read_err:
	mov	$0,%ax
	mov	$0,%dx
	int	$0x13
	jmp	read_sec
#===============================================================================
kill_motor:
	mov	$0x3f2,%dx
	xor	%al,%al
	out	%al,(%dx)
	ret
#===============================================================================
disp_boot:
	mov	$msg_len,%cx

	mov	$boot_msg,%bp
	call	disp_str
	ret

boot_msg:
	.ascii "\n\rBooting "
msg_len	= (. - boot_msg)
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
copy_size:
	cld
	mov	$img_sec,%si
	mov	$P_LOAD_SEC,%di
	mov	$LOAD_SEG,%ax
	mov	%ax,%es
	movsw
	movsw
	ret	
#===============================================================================
	.org	506
img_sec:.word	0,0
	.org	510
	.word	0xAA55			# Boot flag to 1st sector end
#===============================================================================
