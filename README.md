heapdump14
==========

Heap dump reader &amp; visualizer for Go 1.4

You call debug.WriteHeapDump(fd uintptr) to write a heap dump to the given
file descriptor from within your Go program (that's runtime/debug).

The code in this directory is for a hview utility which reads a dump file
(and optionally a binary that generated it), computes interesting data
about the heap, and and presents the data to a web browser.

cd hview
go build
./hview heapdump [binary]

then navigate a browser to localhost:8080 and poke around.
