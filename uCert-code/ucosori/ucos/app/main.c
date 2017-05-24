/* =================================================================================================== */
/* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
/* =================================================================================================== */
#include "includes.h"

#define  TASK_STK_SIZE                1024       /* Size of each task's stacks (# of WORDs)            */
#define  N_TASKS                        10       /* Number of identical tasks                          */

OS_STK           TaskStk[N_TASKS][TASK_STK_SIZE];     /* Tasks stacks                                  */

static  void  Task1(void * pParam);
static  void  Task2(void * pParam);
static  void  Task3(void * pParam);

//int app_efs(void);

void app(void)
{
	int	LineNo10 = 5;
	int	LineNo11 = 7;
	
	con_clrscr(BLANK_ATTR);
	con_gotoxy(0, 0);
	con_putstr(7, 2, 14, "Welcome to Micro-C/OS-II on x86 in protected mode! => UCOS + EFSL");
	con_putstr(2, 19, 12, "  Now there are 2 files , you can read the NOTE to operate these !");
	

	con_putstr(2, 20, 15, "  NOTE:");
	con_putstr(2, 21, 15, "  Press 1 to write and read file1");
	con_putstr(2, 24, 15, "  Press 2 to write and read file2 , then clear it ");
	con_putstr(2, 22, 15, "  Press c to copy file1");
	con_putstr(2, 23, 15, "  Press d to clear file1");
	
	OSTaskCreate(Task1, (void *)&LineNo10, &TaskStk[0][TASK_STK_SIZE], 0);
	OSTaskCreate(Task2, (void *)&LineNo11, &TaskStk[1][TASK_STK_SIZE], 2);
	//OSTaskCreate(Task3, 0, &TaskStk[2][TASK_STK_SIZE], 3);
	OSStart();					   /* Start multitasking                       */
}

void Task1(void * pParam)
{
	int LineNo = *(int *) pParam, k = 0;
	char msg[20], cs[] = "|/-\\";

	os_set_tick(OS_TICKS_PER_SEC);			/* Reprogram tick rate                         */
	
	while (1) 
	{
		sprintf(msg, "Under working %c", cs[k ++]);
		con_putstr(30, LineNo, 14, msg);
		k %= 4;
		OSTimeDlyHMSM(0,0,0,600);	//time delay for 120ms
	}
}

void Task2(void * pParam)
{
	int LineNo = *(int *) pParam, k = 0;
	char msg[20];

	while (1) 
	{
		sprintf(msg, "Under working %d", ++ k);
		con_putstr(30, LineNo, 14, msg);
		k %= 4;
		OSTimeDlyHMSM(0,0,0,60);	//time delay for 120ms
	}
}

//void Task3(void * pParam)
//{
//	app_efs();
//	OSTaskDel(3);
//}

void main (void)
{
	app();
}
