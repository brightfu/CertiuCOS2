/* ========================================================================== */
/* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
/* ========================================================================== */
#ifndef	__TYPE_H__
#define	__TYPE_H__

#ifndef TRUE
#define TRUE  		1
#endif

#ifndef FALSE
#define FALSE 		0
#endif

#ifndef NULL
#define NULL ((void *) 0)
#endif

typedef char * va_list;

typedef unsigned long long u64;
typedef unsigned int u32;
typedef unsigned short u16;
typedef unsigned char u8;

typedef void (*P_VFUNC)();
typedef int (*P_IFUNC)();

#endif	/* __TYPE_H__ */
