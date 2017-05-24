/* =================================================================================================== */
/* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
/* =================================================================================================== */
#include "includes.h"


void setup_kernel()
{
	OSInit();					/* Initialize uC/OS-II                         */
	os_setvect(uCOS, OSCtxSw);			/* Install uC/OS-II's context switch vector    */
	OS_ENTER_CRITICAL();
	os_setvect(0x20, OSTickISR);			/* Install uC/OS-II's clock tick ISR           */
	
	//os_setvect(0x21, OSKBISR);

	
	OS_EXIT_CRITICAL();
}
