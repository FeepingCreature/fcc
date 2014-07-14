The memory profiler (std.memprof) logs every allocation and free to a dump file. The file has the extension .txt, despite not being a text file "as such". This file documents the memprof format.

Format
======

A memprof-format file contains a number of entries. Each entry starts with a character indicating the nature of the entry, and contains a dynamic number of fields. This can be either:

"*": introduces a stackframe label.
"+": logs an allocation and its backtrace
"-": logs a free

The format of "*" is: size_t stringlen, and a string of that length describing the stackframe.

The format of "+" is: void* pointer_allocated, size_t alloc_size, size_t idlen, and a bunch of ids, which are indexes into the implied array created by previous "*"s, describing a backtrace, with 0 being the memory allocator and the last entry (usually) being main.

The format of "-" is: void* pointer_freed. Size is implied by a previous "+".

Tools
=====

There are two associated tools, utils/memfix.nt and utils/memprint.nt.

memfix takes a memprof file and removes allocations that were later freed, reducing the size of the file. It also prints the number of bytes leaked (allocated but never freed).

memprint takes a memprof file and prints a treeview of allocations, ordered by size. It has a known crashing bug, which I was unable to find, but is usually good enough to at least give some useful output. (Sorry.)
