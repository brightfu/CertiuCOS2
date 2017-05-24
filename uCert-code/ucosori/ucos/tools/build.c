/* ========================================================================== */
/* Author: Qu Bo <qu99adm@126.com> <http://www.qu99.net> */
/* ========================================================================== */
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>

void die(char * str)
{
	fprintf(stderr, "%s\n", str);
	exit(1);
}

int main(int argc, char ** argv)
{
	int i, c, id, hs, ks;
	struct stat st;
	unsigned char buf[512];

	if (argc == 4) {
		/* Build boot sectors */
		if ((id = open(argv[1], O_RDONLY, 0)) < 0)
			die("Unable to open boot file ...");
		if ((i = read(id, buf, 512)) != 512 ||
			buf[510] != 0x55 || buf[511] != 0xAA) {
			die("not a boot block ...");
		}
		stat(argv[2],&st);
		hs = *(short *)&buf[506] = (st.st_size + 511) / 512;
		stat(argv[3],&st);
		ks = *(short *)&buf[508] = (st.st_size + 511) / 512;
		if ((i = write(1,buf,512)) != 512)
			die("Write call failed");
		fprintf(stderr, "=== Boot:\t%d bytes (1 sector).\n", i);
		close(id);
		/* Build loader sectors */
		if ((id = open(argv[2], O_RDONLY, 0)) < 0)
			die("Unable to open loader file ...");
		for (i = 0 ; (c = read(id, buf, 512)) >0 ; i += c)
			if (write(1, buf, c) != c)
				die("Write call failed");
		close(id);
		fprintf(stderr, "=== loader:\t%d bytes (%d sectors).\n", i, hs);
		for (buf[0] = '\0', c = hs << 9; i < c; i ++)
			if (write(1, buf, 1) != 1)
				die("Write call failed");
		/* Build kernel sectors */
		if ((id = open(argv[3], O_RDONLY, 0)) < 0)
			die("Unable to open 'kernel'");
		for (i = 0 ; (c = read(id, buf, 512)) > 0; i += c)
			if (write(1, buf, c) != c)
				die("Write call failed");
		close(id);
		fprintf(stderr, "=== Kernel:\t%d bytes (%d sectors).\n", i, ks);
		for (buf[0] = '\0', c = ks << 9; i < c; i ++)
			if (write(1, buf, 1) != 1)
				die("Write call failed");
		memset(buf,0,512);
		for (i = hs + ks + 1; i < 2880; i ++)
			if (write(1, buf, 512) != 512)
				die("Write call failed");
	} else {
		die("Usage: build booter loader kernel [> image]");
	}
	return(0);
}
