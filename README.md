## Intro

VCC is a mechanical verifier for concurrent C programs. VCC takes a C program,
annotated with function specifications, data invariants, loop invariants, and
ghost code, and tries to prove these annotations correct. If it succeeds, VCC
promises that your program actually meets its specifications.

## Features

* VCC is **sound** -- if VCC verifies your program, it really is correct (modulo bugs in VCC itself).
* VCC verification is **modular** -- VCC verifies your program one function/type definition at a time, using only the specifications of the functions it calls and the data structures it uses. This means that you can verify your code even if the functions you call haven't been written yet.
* VCC supports **concurrency** -- you can use VCC to verify programs that use both coarse-grained and fine-grained concurrency. You can even use it to verify your concurrency control primitives. Verifying a function implicitly guarantees its thread safety in any concurrent environment that respects the contracts on its functions and data structures.
* VCC supports **low-level C** features (e.g. bitfields, unions, wrap-around arithmetic). 

## Getting Started

You get a taste of VCC by running it in your browser from 
[RiSE4Fun website](http://rise4fun.com/vcc). (Note however that this version is not
updated very often.)


## Papers

* *Verifying Concurrent C Programs with VCC.*  
  Ernie Cohen, Mark Hillebrand, Michał Moskal, Wolfram Schulte, Stephan Tobies. 
  [PDF print](https://research.microsoft.com/en-us/um/people/moskal/pdf/vcc-tutorial-col2.pdf)
  [PDF screen](https://research.microsoft.com/en-us/um/people/moskal/pdf/vcc-tutorial-col1w.pdf)
* *The VCC Manual* 
  [PDF print](https://research.microsoft.com/en-us/um/people/moskal/pdf/vcc-manual-col2.pdf)
  [PDF screen](https://research.microsoft.com/en-us/um/people/moskal/pdf/vcc-manual-col1w.pdf)
  (A working draft of the VCC manual.)
* *VCC: A Practical System for Verifying Concurrent C.*  
  Ernie Cohen, Markus Dahlweid, Mark Hillebrand, Dirk Leinenbach, Michał Moskal, Thomas Santen, Wolfram Schulte, Stephan Tobies. 
  22nd International Conference on Theorem Proving in Higher Order Logics (TPHOLs 2009). (LNCS 5674). 
  [PDF](https://research.microsoft.com/en-us/um/people/moskal/pdf/tphol2009.pdf)
  (Provides a good overall system description of VCC; the paper to cite for VCC)
* *Local Verification of Global Invariants in Concurrent Programs.* 
  Ernie Cohen, Michał Moskal, Wolfram Schulte, Stephan Tobies. Computer Aided Verification (CAV2010). 
  [PDF](https://research.microsoft.com/en-us/um/people/moskal/pdf/local.pdf) 
  (The best description of the underlying methodology)
* *A Practical Verification Methodology for Concurrent Programs.*  
  Ernie Cohen, Michał Moskal, Wolfram Schulte, Stephan Tobies. MSR-TR-2009-15. 
  [PDF](https://research.microsoft.com/en-us/um/people/moskal/pdf/concurrency3.pdf]
  (The methodological description is out-of-date, but this provides some detail on how programs are actually verified).
* *A Precise Yet Efficient Memory Model For C.*  
  Ernie Cohen, Michał Moskal, Wolfram Schulte, Stephan Tobies. 
  4th International Workshop on Systems Software Verification (SSV2009). 
  [PDF] (https://research.microsoft.com/en-us/um/people/moskal/pdf/ssv2009.pdf)
  (Describes the VCC typestate)


