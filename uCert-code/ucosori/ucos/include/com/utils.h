/* =================================================================================================== */
/* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
/* =================================================================================================== */
#ifndef __UTILS_H__
#define __UTILS_H__

/* 8253/8254 PIT (Programmable Interval Timer) */
#define TIMER_FREQ	2386360L	/* clock frequency for timer in PC and AT */

#define con_putchar scr_char
#define con_putstr  scr_str
#define con_clrscr  clrscr
#define con_gotoxy  set_cursor

#define os_memcpy memcpy
#define os_memset memset

int  sprintf(char *out, const char *format, ...);
int  printk(const char *format, ...);
void memset(void *buf, char chr, int n);
void memcpy(void *dest, const void *src, int n) ;

void os_set_tick(unsigned short freq);

unsigned char inb(int port);
int outb(unsigned char val, int port);
void os_setvect(int vectno, void (*isr)(void));
void *os_getvect(int vectno);

#endif	/* __UTILS_H__ */
