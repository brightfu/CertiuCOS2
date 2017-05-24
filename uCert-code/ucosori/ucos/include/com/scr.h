/* =================================================================================================== */
/* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
/* =================================================================================================== */
#ifndef __SCR_H__
#define __SCR_H__

#define MAX_LINES	25
#define MAX_COLUMNS	80
#define TAB_WIDTH	8			/* must be power of 2 */

/* color text mode, the video ram starts from 0xb8000,
   we all have color text mode, right? :) */
#define VIDEO_RAM	0xb8000

#define LINE_RAM	(MAX_COLUMNS*2)

#define PAGE_RAM	(MAX_LINE*MAX_COLUMNS)

#define BLANK_CHAR	(' ')
#define BLANK_ATTR	(0x07)		/* white fg, black bg */

#define CHAR_OFF(x,y)	(LINE_RAM*(y)+2*(x))

typedef enum COLOUR_TAG {
	BLACK, BLUE, GREEN, CYAN, RED, MAGENTA, BROWN, WHITE,
	GRAY, LIGHT_BLUE, LIGHT_GREEN, LIGHT_CYAN, 
	LIGHT_RED, LIGHT_MAGENTA, YELLOW, BRIGHT_WHITE
} COLOUR;

void clrscr(unsigned char color);
void set_cursor(int, int);
void get_cursor(int *, int *);
void put_char(char);
void put_str(char *);
void scr_char(char chr, int x, int y, int color);
void scr_str(int x, int y, int color, char *str);

void print_c(char, COLOUR, COLOUR);
#endif	/* __SCR_H__ */
