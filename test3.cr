module test3;

import sys, std.c.setjmp;

void main(int argc, char** argv) {
	jmp_buf buffer;
	int i;
	setjmp buffer;
	i++;
	writeln "$i";
	if (i < 10) { longjmp (buffer, 0); }
}
