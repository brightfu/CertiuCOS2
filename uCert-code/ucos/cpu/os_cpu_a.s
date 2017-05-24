#===============================================================================
#                                     uC/OS-II
#                               The Real-Time Kernel
#                 (c) Copyright 1992-2002, Jean J. Labrosse, Weston, FL
#                                All Rights Reserved
#===============================================================================
#                               80x86 protected code
#                                 (with as and gcc)
# File	: OS_CPU_A.ASM
#===============================================================================
.globl OSStartHighRdy,OSCtxSw,OSIntCtxSw,OSTickISR,OSKBISR
#===============================================================================
.code32
.text

#===============================================================================
OSStartHighRdy: 
	call	OSTaskSwHook		# Call user defined task switch hook
	mov	$1,%al			# OSRunning = TRUE;
	mov	%al,OSRunning
	mov	OSTCBHighRdy,%ebx
	mov	(%ebx),%esp		# Switch the task stack
	popal
        popfl
	ret				# Run task
#===============================================================================
OSCtxSw:                # Task switching from task level
	pushfl
        pushal				# Save current task's context
	mov	OSTCBCur,%ebx
	mov	%esp,(%ebx)		# OSTCBCur->OSTCBStkPtr = ESP
	call	OSTaskSwHook		# Call user defined task switch hook
	mov	OSTCBHighRdy,%eax	# OSTCBCur <= OSTCBHighRdy
	mov	%eax,OSTCBCur
	mov	OSPrioHighRdy,%al	# OSPrioCur <= OSPrioHighRdy
	mov	%al,OSPrioCur
	mov	OSTCBHighRdy,%ebx	# ESP = OSTCBHighRdy->OSTCBStkPtr
	mov	(%ebx),%esp
	popal
        popfl
	ret				# Return to new task
#===============================================================================
OSIntCtxSw:				# Task switching from an ISR
	call	OSTaskSwHook		# Call user defined task switch hook
	mov	OSTCBHighRdy,%eax	# OSTCBCur = OSTCBHighRdy
	mov	%eax,OSTCBCur
	mov	OSPrioHighRdy,%al	# OSPrioCur = OSPrioHighRdy
	mov	%al,OSPrioCur
	mov	OSTCBHighRdy,%ebx	# SS:SP = OSTCBHighRdy->OSTCBStkPtr
	mov	(%ebx),%esp
	popal
	iret				# Return to new task
#===============================================================================
OSTickISR: 
	pushal				# Save interrupted task's context
	incb	OSIntNesting		# Notify uC/OS-II of ISR
#	cmpb	$1,OSIntNesting		# if (OSIntNesting == 1)
#	jnz	1f
#	mov	OSTCBCur,%ebx
#	mov	%esp,(%ebx)		# OSTCBCur->OSTCBStkPtr = (SS):ESP
1:	mov	$0x20,%al		# Move EOI code into AL.
	mov	$0x20,%dx		# Address of 8259 PIC in DX.
	out	%al,%dx			# Send EOI to PIC if not processing DOS timer.
	call	OSTimeTick		# Process system tick
	
	
	
	call	OSIntExit		# Notify uC/OS-II of end of ISR
	popal
	iret				# Return to interrupted task
#===============================================================================


