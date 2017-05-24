/* =================================================================================================== */
/* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
/* =================================================================================================== */
#include "includes.h"

#define va_next(ap) (((unsigned *)((ap)+=sizeof(unsigned)))[-1])

static int n2a(char *buff, unsigned i, unsigned base)
{
	char ch, *p = buff;
	while (*p ++ = (i % base) + 0x30, i /= base);
	for (i = p - buff, *p -- = '\0'; buff < p; ch = *buff, *buff ++ = *p, *p -- = ch);
	return i;
}

static int x2a(char *buff, unsigned int i) {
	char ch, *p = buff + 7;
	for (; *p -- = (ch = (i & 0x0f)) + (ch > 9 ? 0x37 : 0x30), p >= buff; i >>= 4);
	return 8;
}

/*=============================================================================
 * format: %[type], type: s,c,x,d
 *===========================================================================*/
int vsprintf(char *buff, const char *fmt, va_list args)
{
	int i = 0;
	char *s, *p = buff;

	for (; fmt[i]; ++i) {
		if ((fmt[i]!='%') && (fmt[i]!='\\')) {
			*p ++ = fmt[i];
			continue;
		} else if (fmt[i] == '\\') {
			/* \a \b \t \n \v \f \r \\ */
			switch (fmt[++i]) {
			case 'a': *p ++ = '\a'; break;
			case 'b': *p ++ = '\b'; break;
			case 't': *p ++ = '\t'; break;
			case 'n': *p ++ = '\n'; break;
			case 'r': *p ++ = '\r'; break;
			case '\\':*p ++ = '\\'; break;
			}
			continue;
		}
		/* fmt[i] == '%' */
		switch (fmt[++i]) {
		case 's':
			s = (char *)va_next(args);
			while (*s)
				*p ++ = *s++;
			break;
		case 'c':
			*p ++ = (char)va_next(args);
			break;
		case 'x':
			p += x2a(p, (unsigned long)va_next(args));
			break;
		case 'd':
			p += n2a(p, (unsigned long)va_next(args), 10);
			break;
		case '%':
			*p ++ = '%';
			break;
		default:
			*p ++ = fmt[i];
			break;
		}
	}
	*p = '\0';
	return p - buff;
}

int sprintf(char *out, const char *format, ...)
{
	va_list arg = (va_list)((char*)(&format) + 4);
	return vsprintf(out, format, arg);
}

int printk(const char *format, ...)
{
	int i;
	char buff[256];
	va_list arg = (va_list)((char*)(&format) + 4);
	
	i = vsprintf(buff, format, arg);
	put_str(buff);
	return i;
}

void memcpy(void *dst, const void *src, int size)
{
	unsigned char *d = dst;
	const unsigned char *s = src;
	for (; size -- > 0; *d ++ = *s ++);
}

void memset(void *cs, char c, int size)
{
	unsigned char *s = cs;
	for (; size -- > 0; *s ++ = c);
}

void os_set_tick(unsigned short freq)
{
	int count = (freq > 0) ? ((TIMER_FREQ / freq + 1) >> 1) : 0;
	
	OS_ENTER_CRITICAL();
	outb(0x36, 0x43);		/* binary, mode 3, LSB/MSB, ch 0 */
	outb(count & 0xff, 0x40);	/* LSB */
	outb(count >> 8, 0x40);		/* MSB */
	OS_EXIT_CRITICAL();
}
