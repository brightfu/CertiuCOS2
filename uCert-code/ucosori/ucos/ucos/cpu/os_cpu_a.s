#===============================================================================
# /* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
#===============================================================================
#                                     uC/OS-II
#                               The Real-Time Kernel
#                 (c) Copyright 1992-2002, Jean J. Labrosse, Weston, FL
#                                All Rights Reserved
#===============================================================================
#                               80x86 protected code
#                                 (with as and gcc)
# File	: OS_CPU_A.ASM
# By	: Qu Bo
#===============================================================================
.globl OSStartHighRdy,OSCtxSw,OSIntCtxSw,OSTickISR,OSKBISR
#===============================================================================
.code32
.text
#===============================================================================
#                                START MULTITASKING
#                             void OSStartHighRdy(void)
#
# The stack frame is assumed to look as follows:
#
# OSTCBHighRdy->OSTCBStkPtr --> DS				(Low memory)
#                               ES
#                               EDI
#                               ESI
#                               EBP
#                               ESP
#                               EBX
#                               EDX
#                               ECX
#                               EAX
#                               OFFSET  of task code address
#                               SEGMENT of task code address
#                               Flags to load in PSW
#                               OFFSET  of task code address
#                               SEGMENT of task code address
#                               OFFSET  of 'pdata'
#                               SEGMENT of 'pdata'		(High memory)
#
# Note : OSStartHighRdy() MUST:
#           a) Call OSTaskSwHook() then,
#           b) Set OSRunning to TRUE,
#           c) Switch to the highest priority task.
#===============================================================================
OSStartHighRdy: 
	call	OSTaskSwHook		# Call user defined task switch hook
	mov	$1,%al			# OSRunning = TRUE;
	mov	%al,OSRunning
	mov	OSTCBHighRdy,%ebx
	mov	(%ebx),%esp		# Switch the task stack
#	pop	%ds			# Load task's context
#	pop	%es
	popal
	iret				# Run task
#===============================================================================
#                      PERFORM A CONTEXT SWITCH (From task level)
#                                 void OSCtxSw(void)
#
# Note(s): 1) Upon entry,
#             OSTCBCur     points to the OS_TCB of the task to suspend
#             OSTCBHighRdy points to the OS_TCB of the task to resume
#
#          2) The stack frame of the task to suspend looks as follows:
#
#                 SP -> OFFSET  of task to suspend    (Low memory)
#                       SEGMENT of task to suspend
#                       PSW     of task to suspend    (High memory)
#
#          3) The stack frame of the task to resume looks as follows:
#
# OSTCBHighRdy->OSTCBStkPtr --> DS				(Low memory)
#                               ES
#                               EDI
#                               ESI
#                               EBP
#                               ESP
#                               EBX
#                               EDX
#                               ECX
#                               EAX
#                               ADDRESS of task code
#                               Flags to load in EPSW		(High memory)
#===============================================================================
OSCtxSw:				# Task switching from task level
	pushal				# Save current task's context
#	push	%es
#	push	%ds
	mov	OSTCBCur,%ebx
	mov	%esp,(%ebx)		# OSTCBCur->OSTCBStkPtr = ESP
	call	OSTaskSwHook		# Call user defined task switch hook
	mov	OSTCBHighRdy,%eax	# OSTCBCur <= OSTCBHighRdy
	mov	%eax,OSTCBCur
	mov	OSPrioHighRdy,%al	# OSPrioCur <= OSPrioHighRdy
	mov	%al,OSPrioCur
	mov	OSTCBHighRdy,%ebx	# ESP = OSTCBHighRdy->OSTCBStkPtr
	mov	(%ebx),%esp
#	pop	%ds			# Load new task's context
#	pop	%es
	popal
	iret				# Return to new task
#===============================================================================
#                                PERFORM A CONTEXT SWITCH (From an ISR)
#                                        void OSIntCtxSw(void)
#
# Note(s): 1) Upon entry,
#             OSTCBCur     points to the OS_TCB of the task to suspend
#             OSTCBHighRdy points to the OS_TCB of the task to resume
#
#          2) The stack frame of the task to suspend looks as follows:
#
# OSTCBCur->OSTCBStkPtr ------>  DS				(Low memory)
#                                ES
#                                DI
#                                SI
#                                BP
#                                SP
#                                BX
#                                DX
#                                CX
#                                AX
#                                OFFSET  of task code address
#                                SEGMENT of task code address
#                                Flags to load in PSW		(High memory)
#
#
#          3) The stack frame of the task to resume looks as follows:
#
# OSTCBHighRdy->OSTCBStkPtr --> DS				(Low memory)
#                               ES
#                               DI
#                               SI
#                               BP
#                               SP
#                               BX
#                               DX
#                               CX
#                               AX
#                               OFFSET  of task code address
#                               SEGMENT of task code address
#                               Flags to load in PSW		(High memory)
#===============================================================================
OSIntCtxSw:				# Task switching from an ISR
	call	OSTaskSwHook		# Call user defined task switch hook
	mov	OSTCBHighRdy,%eax	# OSTCBCur = OSTCBHighRdy
	mov	%eax,OSTCBCur
	mov	OSPrioHighRdy,%al	# OSPrioCur = OSPrioHighRdy
	mov	%al,OSPrioCur
	mov	OSTCBHighRdy,%ebx	# SS:SP = OSTCBHighRdy->OSTCBStkPtr
	mov	(%ebx),%esp
#	pop	%ds			# Load new task's context
#	pop	%es
	popal
	iret				# Return to new task
#===============================================================================
#                                  HANDLE TICK ISR
#
# Description: This function is called 199.99 times per second or, 11 times
#              faster than the normal DOS tick rate of 18.20648 Hz.
#              Thus every 11th time, the normal DOS tick handler is called.
#              This is called chaining.  10 times out of 11, however,
#              the interrupt controller on the PC must be cleared to allow
#              for the next interrupt.
#
# Arguments  : none
#
# Returns    : none
#
# Note(s)    : The following C-like pseudo-code describe the operation being
#              performed in the code below.
#
#              Save all registers on the current task's stack;
#              OSIntNesting++;
#              if (OSIntNesting == 1) {
#                 OSTCBCur->OSTCBStkPtr = SS:SP
#              }
#              OSTickDOSCtr--;
#              if (OSTickDOSCtr == 0) {
#                  OSTickDOSCtr = 11;
#                  INT 81H;             Chain into DOS every 54.925 mS
#                                       (Interrupt will be cleared by DOS)
#              } else {
#                  Send EOI to PIC;     Clear tick interrupt by sending an
#                                       End-Of-Interrupt to the 8259
#                                       PIC (Priority Interrupt Controller)
#              }
#              OSTimeTick();            Notify uC/OS-II that a tick has occured
#              OSIntExit();             Notify uC/OS-II about end of ISR
#              Restore all registers that were save on the current task's stack;
#              Return from Interrupt;
#===============================================================================
#
OSTickISR: 
	pushal				# Save interrupted task's context
#	push	%es
#	push	%ds
	incb	OSIntNesting		# Notify uC/OS-II of ISR
	cmpb	$1,OSIntNesting		# if (OSIntNesting == 1)
	jnz	1f
	mov	OSTCBCur,%ebx
	mov	%esp,(%ebx)		# OSTCBCur->OSTCBStkPtr = (SS):ESP
1:	mov	$0x20,%al		# Move EOI code into AL.
	mov	$0x20,%dx		# Address of 8259 PIC in DX.
	out	%al,%dx			# Send EOI to PIC if not processing DOS timer.
	call	OSTimeTick		# Process system tick
	
	
	
	call	OSIntExit		# Notify uC/OS-II of end of ISR
#	pop	%ds			# Restore interrupted task's context
#	pop	%es
	popal
	iret				# Return to interrupted task
#===============================================================================


