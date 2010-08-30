module hello;
import sys;

alias FF = 0xff;

int main(int argc, char** argv) {
  writeln("Hello World");
  int a = 1_024;
  writeln("0 is $(0), 0xff_ff  is $(0xff_ff), 0_777 is $(0_777), 0b1_001 is $(0b1_001). a is $a. ");
  return 0;
}
