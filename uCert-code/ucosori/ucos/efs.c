#include <stdio.h>
#include <efs.h>
#include <ls.h>
#include "includes.h"
	EmbeddedFileSystem efs;
	EmbeddedFile file;	
	EmbeddedFile file2;
	DirList dlist;
	unsigned short i;
	char buf[512];
	char buf2[512];
int app_efs(void)
{	
	if(efs_init(&efs,"")!=0){
		printk("Could not open filesystem.\n");
		return(-1);
	}
	
	if(file_fopen(&file,&efs.myFs,"a.txt",'w')!=0){
		
		printk("Could not create file.\n");
		return(-2);
	}
	
	if(mkdir(&efs.myFs,"dir")==0)
		{
		printk("  MAKE A NEW DIRECTORY : dir/subdir1\n");
		mkdir(&efs.myFs,"dir/subdir1");
		}
	fs_umount(&efs.myFs);
	
	memset(buf, 0, 512);
	for (i = 0; i < 10; i ++)
		buf[i] = i + 48;
	file_write(&file,512,buf);
	file_fclose(&file);
	//memset(buf, 0, 512);
	
	if(file_fopen(&file,&efs.myFs,"a.txt",'r')!=0){
		printk("Could not open file.\n");
		return(-2);
	}
	
	file_read(&file,512,buf);
	file_fclose(&file);


	buf[64] = 0;
	printk(" .Now the file1 is: %s\n", buf);
	
	return(0);
}


void copy1(void)
{		int j=0;
		for(j=0;j<10;j++)
		{buf[j+10] = buf[j];}
	file_write(&file,512,buf);
	file_fclose(&file);	
		
	file_read(&file,512,buf);
	file_fclose(&file);
	printk("  Copy file1 : %s\n", buf);
}

void clear1(void)
{
	memset(buf, 0, 512);
	file_write(&file,512,buf);
	file_fclose(&file);
	
	file_read(&file,512,buf);
	file_fclose(&file);
	printk("  Clear file1 and buffer.\n Now the file1 is: %s\n", buf);
	
}
void writefile2(void)
{	
	
	for (i = 0; i < 10; i ++)
		buf2[i] = i + 65;
	file_write(&file2,512,buf2);
	file_fclose(&file2);	
	file_read(&file2,512,buf2);
	file_fclose(&file2);
	printk(" .Now the file2 is: %s\n", buf2);
	
	memset(buf2, 0, 512);
	file_write(&file2,512,buf2);
	file_fclose(&file2);
	file_read(&file2,512,buf2);
	file_fclose(&file2);
	printk("  Clear file2 and buffer.\n Now the file2 is: %s\n", buf2);
}
void removefile1(void)
{	rmfile(&efs.myFs,"a.txt");
	fs_umount(&efs.myFs);
	printk("  Now the file1 has been removed ,you can press 1 to do it again \n");
}