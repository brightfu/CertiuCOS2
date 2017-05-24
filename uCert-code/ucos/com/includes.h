/* =================================================================================================== */
/* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
/* =================================================================================================== */
/*
*********************************************************************************************************
*                                                uC/OS-II
*                                          The Real-Time Kernel
*
*                        (c) Copyright 1992-1998, Jean J. Labrosse, Plantation, FL
*                                           All Rights Reserved
*
*                                                  V2.52
*
* File     : uCOS_II.H
* By       : Jean J. Labrosse
* Ported By: Qu Bo
*********************************************************************************************************
*/

#include    "os_cpu.h"
#include    "os_cfg.h"
#include    "ucos_ii.h"

#include "com/utils.h"
#include "com/scr.h"
#define MAXQSIZE 128
typedef struct queue{
char buffer[MAXQSIZE];
int front;
int rear;
}queue;