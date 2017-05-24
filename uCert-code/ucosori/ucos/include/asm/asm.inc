#===============================================================================
# /* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
#===============================================================================
# GDT Descriptor Attributes
#     DA_  : Descriptor Attribute
#     D    : Data Segment		C    : Code Segment
#     S    : System Segment
#     R    : Read-only			RW   : Read/Write
#     A    : Access 
#===============================================================================
# Segment Granularity
DA_32		= 0x4000		# 32-bit segment
DA_4K		= 0x8000		# 4KB segment	
#===============================================================================
# Descriptor privilege level
DA_DPL0		= 0x00			# DPL = 0
DA_DPL1		= 0x20			# DPL = 1
DA_DPL2		= 0x40			# DPL = 2
DA_DPL3		= 0x60			# DPL = 3
#===============================================================================
# GDT Code- and Data-Segment Types
DA_DR		= 0x90			# Read-Only
DA_DRW		= 0x92			# Read/Write
DA_DRWA 	= 0x93			# Read/Write, accessed
DA_C		= 0x98			# Execute-Only
DA_CR		= 0x9A			# Execute/Read
DA_CCO		= 0x9C			# Execute-Only, conforming
DA_CCOR		= 0x9E			# Execute/Read-Only, conforming
#===============================================================================
# GDT System-Segment and Gate-Descriptor Types
DA_LDT		= 0x82			# LDT
DA_TaskGate	= 0x85			# Task Gate
DA_386TSS	= 0x89			# 32-bit TSS(Available)
DA_386CGate	= 0x8C			# 32-bit Call Gate
DA_386IGate	= 0x8E			# 32-bit Interrupt Gate
DA_386TGate	= 0x8F			# 32-bit Trap Gate
#===============================================================================
# Selector Attributes (Requested privilege level & Table indicator)
SA_RPL0		= 0			# Level 0
SA_RPL1		= 1			# Level 1
SA_RPL2		= 2			# Level 2
SA_RPL3		= 3			# Level 3
SA_TIG		= 0			# For GDT
SA_TIL		= 4			# For LDT
#===============================================================================
# Paging Attributes
PG_P		= 1			# Page existing
PG_RWR		= 0			# R/W Read/Execute
PG_RWW		= 2			# R/W Read/Write/Execute
PG_USS		= 0			# U/S System level
PG_USU		= 4			# U/S User level
#===============================================================================
# MACROS
#===============================================================================
# Segment Descriptor data structure.
#   Usage: Descriptor Base, Limit, Attr
#    Base:  long 
#    Limit: long (low 20 bits available)
#    Attr:  word (lower 4 bits of higher byte are always 0)
.macro Descriptor Base, Limit, Attr
	.word	\Limit & 0xFFFF
	.word	\Base & 0xFFFF
	.byte	(\Base >> 16) & 0xFF
	.word	((\Limit >> 8) & 0xF00) | (\Attr & 0xF0FF)
	.byte	(\Base >> 24) & 0xFF
.endm
# Interrupt Gate data structure.
#   Usage: Gate Selector, Handler, Attr
#    Selector:  word 
#    Handler: long
#    Attr:  word
.macro Gate Selector, Handler, Attr
	.word	\Handler & 0xFFFF
	.word	\Selector
	.word	\Attr & 0xFF00
	.word	\Handler >> 16
.endm
#===============================================================================
NR_GTDS		= 6			# GDT has 6 descriptors
NR_IDTS		= 256			# IDT has 256 descriptors
STACK_TOP	= 0xA0000		# Stack top at 640K
IDT_ADDR	= 0x9D000		# IDT start address
IDT_SIZE	= (NR_IDTS*8)		# IDT has fixed length (0x800)
GDT_ADDR	= (IDT_ADDR+IDT_SIZE)	# GDT starts after IDT
GDT_SIZE	= (NR_GTDS*8)		# GDT length
#===============================================================================
SEL_CS		= 0x08			# Selector for code segment
SEL_DS		= 0x10			# Selector for data segment
SEL_GS		= 0x18			# Selector for kern level video segment
SEL_TSS		= 0x20			# Selector for TSS descriptor in GDT
SEL_LDT		= 0x28			# Selector for LDT descriptor in GDT
#===============================================================================
VIDEO_BASE	= 0x0B8000
KERNEL_BASE	= 0x000000
#===============================================================================
BOOT_SEG	= 0x7C00		/* Stack base address, inner */
LOAD_SEG	= 0x9000		/* Section loading address of loader */
LOAD_OFF	= 0x0200		/* Loading offset of LOADER.BIN */
TEMP_SEG	= 0x1000		/* Section loading address of kernel */
LOAD_BASE	= LOAD_SEG * 0x10
TEMP_BASE	= TEMP_SEG * 0x10
#===============================================================================
P_LOAD_SEC	= 506			# Sectors of loader
P_KERN_SEC	= 508			# Sectors of kernel
P_KERN_OFF	= 510			# Offset of kernel in image file
#===============================================================================
