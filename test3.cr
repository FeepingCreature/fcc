module test3;

import sys;
c_include "setjmp.h";

void main(int argc, char** argv) {
	jmp_buf buffer;
	int i;
	setjmp buffer;
	i++;
	writeln "$i";
	if (i < 10) { longjmp (buffer, 0); }
}
