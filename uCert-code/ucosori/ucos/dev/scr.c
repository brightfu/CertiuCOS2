/* =================================================================================================== */
/* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
/* =================================================================================================== */
#include "includes.h"

static int csr_x = 0;
static int csr_y = 0;
static int attr = BLANK_ATTR;

static void scroll(int lines) {
	short *p = (short *)(VIDEO_RAM+CHAR_OFF(MAX_COLUMNS-1, MAX_LINES-1));
	int i = MAX_COLUMNS-1;
	memcpy((void *)VIDEO_RAM, (void *)(VIDEO_RAM+LINE_RAM*lines),
		   LINE_RAM*(MAX_LINES-lines));
	for (; i>=0; --i)
		*p-- = (short)((BLANK_ATTR<<8)|BLANK_CHAR);
}

void clrscr(unsigned char color)
{
	short *p = (short *)VIDEO_RAM;
	int cnt = MAX_LINES * MAX_COLUMNS;
	
	while (cnt --)
		*p++ = (short)((color<<8)|BLANK_CHAR);
}

void set_cursor(int x, int y) {
	csr_x = x;
	csr_y = y;
	outb(0x0e, 0x3d4);
	outb(((csr_x+csr_y*MAX_COLUMNS)>>8)&0xff, 0x3d5);
	outb(0x0f, 0x3d4);
	outb(((csr_x+csr_y*MAX_COLUMNS))&0xff, 0x3d5);
}

void get_cursor(int *x, int *y) {
	*x = csr_x;
	*y = csr_y;
}

void set_color(int color)
{
	attr = color;
}

void put_char(char c)
{
	char *p = (char *)VIDEO_RAM+CHAR_OFF(csr_x, csr_y);
	
	switch (c) {
	case '\r':
		csr_x = 0;
		break;
	case '\n':
		for (; csr_x<MAX_COLUMNS; ++csr_x) {
			*p++ = BLANK_CHAR;
			*p++ = attr;
		}
		break;
	case '\t':
		c = csr_x+TAB_WIDTH-(csr_x&(TAB_WIDTH-1));
		c = c<MAX_COLUMNS?c:MAX_COLUMNS;
		for (; csr_x<c; ++csr_x) {
			*p++ = BLANK_CHAR;
			*p++ = attr;
		}
		break;
	case '\b':
		if ((! csr_x) && (! csr_y))
			return;
		if (! csr_x) {
			csr_x = MAX_COLUMNS - 1;
			--csr_y;
		} else
			--csr_x;
		((short *)p)[-1] = (short)((BLANK_ATTR<<8)|BLANK_CHAR);
		break;
	default:
		*p++ = c; 
		*p++ = attr;
		++csr_x;
		break;
	}
	if (csr_x >= MAX_COLUMNS) {
		csr_x = 0;
		if (csr_y < MAX_LINES-1)
			++csr_y;
		else 
			scroll(1);
	}
	set_cursor(csr_x, csr_y);
}

void put_str(char *str)
{
	for (; *str; put_char(*str++));
}

void scr_char(char chr, int x, int y, int color)
{
	char *p = (char *)VIDEO_RAM+CHAR_OFF(x, y);
	*p++ = chr;
	*p = color;
}

void scr_str(int x, int y, int color, char *str)
{
	for (; *str; scr_char(*str++, x++, y, color));
}

