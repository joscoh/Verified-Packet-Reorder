# Verified TCP Packet Reordering

Verification of TCP packet reordering from [libflowmanager](https://github.com/wanduow/libflowmanager) with minor changes to code for verification purposes (documented in code). Some small dependencies from [libtrace](https://research.wand.net.nz/software/libtrace.php) are also included and modified similarly.

To verify, install [Verifast](https://github.com/verifast/verifast) and run the command 
```verifast -disable_overflow_check src/tcp_reorder.c```
There will be "dead code" warnings; these are expected and documented in the code (which is unmodified as much as possible).

For the sequence number comparison, we used [Coq](https://coq.inria.fr/) and [VST](https://github.com/PrincetonUniversity/VST). These files can be verified by installing those tools and using the provided Makefile.
