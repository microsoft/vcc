
#include "vcc2.h"

typedef unsigned int CHUNK;

usebitvectors
unsigned Bitcount (CHUNK Target)
  requires (Target <= 0xFFFFFFFF) //FFFFFFFF)

/*++

Routine Description:

    This procedure counts and returns the number of set bits within
    a the chunk.

Arguments:

    Target - The integer containing the bits to be counted.

Return Value:

    UINT32 - The total number of set bits in Target.

--*/

{   
  spec(	 
	 unsigned T0 = (Target & 1);
	 unsigned T1 = (Target & (1 << 1)) >> 1;
	 unsigned T2 = (Target & (1 << 2)) >> 2;
	 unsigned T3 = (Target & (1 << 3)) >> 3;
	 unsigned T4 = (Target & (1 << 4)) >> 4;
	 unsigned T5 = (Target & (1 << 5)) >> 5;
	 unsigned T6 = (Target & (1 << 6)) >> 6;
	 unsigned T7 = (Target & (1 << 7)) >> 7;
	 unsigned T8 = (Target & (1 << 8)) >> 8;
	 unsigned T9 = (Target & (1 << 9)) >> 9;
	 unsigned T10 = (Target & (1 << 10)) >> 10;
	 unsigned T11 = (Target & (1 << 11)) >> 11;
	 unsigned T12 = (Target & (1 << 12)) >> 12;
	 unsigned T13 = (Target & (1 << 13)) >> 13;
	 unsigned T14 = (Target & (1 << 14)) >> 14;
	 unsigned T15 = (Target & (1 << 15)) >> 15;
	 unsigned T16 = (Target & (1 << 16)) >> 16;
	 unsigned T17 = (Target & (1 << 17)) >> 17;
	 unsigned T18 = (Target & (1 << 18)) >> 18;
	 unsigned T19 = (Target & (1 << 19)) >> 19;
	 unsigned T20 = (Target & (1 << 20)) >> 20;
	 unsigned T21 = (Target & (1 << 21)) >> 21;
	 unsigned T22 = (Target & (1 << 22)) >> 22;
	 unsigned T23 = (Target & (1 << 23)) >> 23;
	 unsigned T24 = (Target & (1 << 24)) >> 24;
	 unsigned T25 = (Target & (1 << 25)) >> 25;
	 unsigned T26 = (Target & (1 << 26)) >> 26;
	 unsigned T27 = (Target & (1 << 27)) >> 27;
	 unsigned T28 = (Target & (1 << 28)) >> 28;
	 unsigned T29 = (Target & (1 << 29)) >> 29;
	 unsigned T30 = (Target & (1 << 30)) >> 30;
	 unsigned T31 = (Target & (unsigned)(1 << 31)) >> 31;
    ) 
    
    assert(Target == 
	   (unsigned)(1 << 31) * T31 +
	   (1 << 30) * T30 +
	   (1 << 29) * T29 +
	   (1 << 28) * T28 +
	   (1 << 27) * T27 +
	   (1 << 26) * T26 +
	   (1 << 25) * T25 +
	   (1 << 24) * T24 +
	   (1 << 23) * T23 +
	   (1 << 22) * T22 +
	   (1 << 21) * T21 +
	   (1 << 20) * T20 +
	   (1 << 19) * T19 +
	   (1 << 18) * T18 +
	   (1 << 17) * T17 +
	   (1 << 16) * T16 +
	   (1 << 15) * T15 +
	   (1 << 14) * T14 +
	   (1 << 13) * T13 +
	   (1 << 12) * T12 +
	   (1 << 11) * T11 +
	   (1 << 10) * T10 +
	   (1 << 9) * T9 +
	   (1 << 8) * T8
	   + 128 * T7 +  64 * T6 +  32 * T5 +  16 * T4
	   + 8 * T3 + 4 * T2 + 2 * T1 + T0
	   );

    //
    // The following algorithm was taken from the AMD publication
    // "Software Opimization Guide for the AMD Hammer Processor",
    // revision 1.19, section 8.6.
    //



    //
    // First break the chunk up into a set of two-bit fields, each
    // field representing the count of set bits.  Each field undergoes
    // the following transformation:
    //
    // 00b -> 00b
    // 01b -> 01b
    // 10b -> 01b
    // 11b -> 10b
    //

//    Target -= (Target >> 1) & 0x5555555555555555;

    Target -= (Target >> 1) & 0x55555555;

    assert(Target == 
	   (1 << 30) * (T31 + T30) +
	   (1 << 28) * (T29 + T28) +
	   (1 << 26) * (T27 + T26) +
	   (1 << 24) * (T25 + T24) +
	   (1 << 22) * (T23 + T22) +
	   (1 << 20) * (T21 + T20) +
	   (1 << 18) * (T19 + T18) +
	   (1 << 16) * (T17 + T16) +
	   (1 << 14) * (T15 + T14) +  
	   (1 << 12) * (T13 + T12) +
	   (1 << 10) * (T11 + T10) +  
	   (1 << 8)  * (T9 + T8) +
	   (1 << 6)  * (T7 + T6) +  
	   (1 << 4)  * (T5 + T4) +
           (1 << 2)  * (T3 + T2) +               
                        T1 + T0
	   );
    
  	//
    // Next, combine the totals in adjacent two-bit fields into a four-bit
    // field.
    //

    //Target = (Target & 0x3333333333333333) +
    //         ((Target >> 2) & 0x3333333333333333);

    Target = (Target & 0x33333333) +
             ((Target >> 2) & 0x33333333);

    assert(Target == 
	   (1 << 28) * (T31 + T30 + T29 + T28) +
	   (1 << 24) * (T27 + T26 + T25 + T24) +
	   (1 << 20) * (T23 + T22 + T21 + T20) +
	   (1 << 16) * (T19 + T18 + T17 + T16) +  
	   (1 << 12) * (T15 + T14 + T13 + T12) +
	   (1 << 8) * (T11 + T10 +  T9 + T8) +
	   (1 << 4) * (T7 + T6 + T5 + T4) +
                       T3 + T2 + T1 + T0);


    //
    // Now, combine adjacent four-bit fields to end up with a set of 8-bit
    // totals.
    //

    Target = (Target + (Target >> 4)) & 0x0F0F0F0F;

    assert(Target == 
	   (1 << 24) * (T31 + T30 + T29 + T28 + T27 + T26 + T25 + T24) + 
	   (1 << 16) * (T23 + T22 + T21 + T20 + T19 + T18 + T17 + T16) +
           (1 << 8)  * (T15 + T14 + T13 + T12 + T11 + T10 +  T9 + T8)  +
	                 T7 + T6 + T5 + T4 + T3 + T2 + T1 + T0);


    //
    // Finally, sum all of the 8-bit totals.  The result will be the
    // number of bits that were set in Target.
    //

    //Target = (Target * 0x0101010101010101) >> 56;

    assert(Target <= 0x08080808);
    
    Target = ((Target * 0x01010101) & 0xFFFFFFFF) >> 24;

    assert(Target == 
	   T31 + T30 + T29 + T28 + T27 + T26 + T25 + T24 + 
	   T23 + T22 + T21 + T20 + T19 + T18 + T17 + T16 +
	   T15 + T14 + T13 + T12 + T11 + T10 +  T9 + T8 +
	   T7 + T6 + T5 + T4 + T3 + T2 + T1 + T0);

    return Target;

}
