
#include "vc.h"

#define PowTwo(i) ((CHUNK)1 << i)

typedef unsigned long long CHUNK;

usebitvectors
CHUNK Bitcount (CHUNK Target)

//  ensures(result < 64)

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
	 CHUNK T0 = (Target & 1);
	 CHUNK T1 = (Target & PowTwo(1)) >> 1;
	 CHUNK T2 = (Target & PowTwo(2)) >> 2;
	 CHUNK T3 = (Target & PowTwo(3)) >> 3;
	 CHUNK T4 = (Target & PowTwo(4)) >> 4;
	 CHUNK T5 = (Target & PowTwo(5)) >> 5;
	 CHUNK T6 = (Target & PowTwo(6)) >> 6;
	 CHUNK T7 = (Target & PowTwo(7)) >> 7;
	 CHUNK T8 = (Target & PowTwo(8)) >> 8;
	 CHUNK T9 = (Target & PowTwo(9)) >> 9;
	 CHUNK T10 = (Target & PowTwo(10)) >> 10;
	 CHUNK T11 = (Target & PowTwo(11)) >> 11;
	 CHUNK T12 = (Target & PowTwo(12)) >> 12;
	 CHUNK T13 = (Target & PowTwo(13)) >> 13;
	 CHUNK T14 = (Target & PowTwo(14)) >> 14;
	 CHUNK T15 = (Target & PowTwo(15)) >> 15;
	 CHUNK T16 = (Target & PowTwo(16)) >> 16;
	 CHUNK T17 = (Target & PowTwo(17)) >> 17;
	 CHUNK T18 = (Target & PowTwo(18)) >> 18;
	 CHUNK T19 = (Target & PowTwo(19)) >> 19;
	 CHUNK T20 = (Target & PowTwo(20)) >> 20;
	 CHUNK T21 = (Target & PowTwo(21)) >> 21;
	 CHUNK T22 = (Target & PowTwo(22)) >> 22;
	 CHUNK T23 = (Target & PowTwo(23)) >> 23;
	 CHUNK T24 = (Target & PowTwo(24)) >> 24;
	 CHUNK T25 = (Target & PowTwo(25)) >> 25;
	 CHUNK T26 = (Target & PowTwo(26)) >> 26;
	 CHUNK T27 = (Target & PowTwo(27)) >> 27;
	 CHUNK T28 = (Target & PowTwo(28)) >> 28;
	 CHUNK T29 = (Target & PowTwo(29)) >> 29;
	 CHUNK T30 = (Target & PowTwo(30)) >> 30;
	 CHUNK T31 = (Target & PowTwo(31)) >> 31;
	 CHUNK T32 = (Target & PowTwo(32)) >> 32;
	 CHUNK T33 = (Target & PowTwo(33)) >> 33;
	 CHUNK T34 = (Target & PowTwo(34)) >> 34;
	 CHUNK T35 = (Target & PowTwo(35)) >> 35;
	 CHUNK T36 = (Target & PowTwo(36)) >> 36;
	 CHUNK T37 = (Target & PowTwo(37)) >> 37;
	 CHUNK T38 = (Target & PowTwo(38)) >> 38;
	 CHUNK T39 = (Target & PowTwo(39)) >> 39;
	 CHUNK T40 = (Target & PowTwo(40)) >> 40;
	 CHUNK T41 = (Target & PowTwo(41)) >> 41;
	 CHUNK T42 = (Target & PowTwo(42)) >> 42;
	 CHUNK T43 = (Target & PowTwo(43)) >> 43;
	 CHUNK T44 = (Target & PowTwo(44)) >> 44;
	 CHUNK T45 = (Target & PowTwo(45)) >> 45;
	 CHUNK T46 = (Target & PowTwo(46)) >> 46;
	 CHUNK T47 = (Target & PowTwo(47)) >> 47;
	 CHUNK T48 = (Target & PowTwo(48)) >> 48;
	 CHUNK T49 = (Target & PowTwo(49)) >> 49;
	 CHUNK T50 = (Target & PowTwo(50)) >> 50;
	 CHUNK T51 = (Target & PowTwo(51)) >> 51;
	 CHUNK T52 = (Target & PowTwo(52)) >> 52;
	 CHUNK T53 = (Target & PowTwo(53)) >> 53;
	 CHUNK T54 = (Target & PowTwo(54)) >> 54;
	 CHUNK T55 = (Target & PowTwo(55)) >> 55;
	 CHUNK T56 = (Target & PowTwo(56)) >> 56;
	 CHUNK T57 = (Target & PowTwo(57)) >> 57;
	 CHUNK T58 = (Target & PowTwo(58)) >> 58;
	 CHUNK T59 = (Target & PowTwo(59)) >> 59;
         CHUNK T60 = (Target & PowTwo(60)) >> 60;
         CHUNK T61 = (Target & PowTwo(61)) >> 61;
         CHUNK T62 = (Target & PowTwo(62)) >> 62;
         CHUNK T63 = (Target & PowTwo(63)) >> 63;
  ) 
    
    assert(Target == 
	   PowTwo(63) * T63 +
	   PowTwo(62) * T62 +
	   PowTwo(61) * T61 +
	   PowTwo(60) * T60 +
	   PowTwo(59) * T59 +
	   PowTwo(58) * T58 +
	   PowTwo(57) * T57 +
	   PowTwo(56) * T56 +
	   PowTwo(55) * T55 +
	   PowTwo(54) * T54 +
	   PowTwo(53) * T53 +
	   PowTwo(52) * T52 +
	   PowTwo(51) * T51 +
	   PowTwo(50) * T50 +
	   PowTwo(49) * T49 +
	   PowTwo(48) * T48 +
	   PowTwo(47) * T47 +
	   PowTwo(46) * T46 +
	   PowTwo(45) * T45 +
	   PowTwo(44) * T44 +
	   PowTwo(43) * T43 +
	   PowTwo(42) * T42 +
	   PowTwo(41) * T41 +
	   PowTwo(40) * T40 +
	   PowTwo(39) * T39 +
	   PowTwo(38) * T38 +
	   PowTwo(37) * T37 +
	   PowTwo(36) * T36 +
	   PowTwo(35) * T35 +
	   PowTwo(34) * T34 +
	   PowTwo(33) * T33 +
	   PowTwo(32) * T32 +
	   PowTwo(31) * T31 +
	   PowTwo(30) * T30 +
	   PowTwo(29) * T29 +
	   PowTwo(28) * T28 +
	   PowTwo(27) * T27 +
	   PowTwo(26) * T26 +
	   PowTwo(25) * T25 +
	   PowTwo(24) * T24 +
	   PowTwo(23) * T23 +
	   PowTwo(22) * T22 +
	   PowTwo(21) * T21 +
	   PowTwo(20) * T20 +
	   PowTwo(19) * T19 +
	   PowTwo(18) * T18 +
	   PowTwo(17) * T17 +
	   PowTwo(16) * T16 +
	   PowTwo(15) * T15 +
	   PowTwo(14) * T14 +
	   PowTwo(13) * T13 +
	   PowTwo(12) * T12 +
	   PowTwo(11) * T11 +
	   PowTwo(10) * T10 +
	   PowTwo(9) * T9 +
	   PowTwo(8) * T8 +
	   PowTwo(7) * T7 +  
           PowTwo(6) * T6 +  
           PowTwo(5) * T5 +
           PowTwo(4) * T4 +
	   PowTwo(3) * T3 + 
           PowTwo(2) * T2 + 
	   PowTwo(1) * T1 + 
	   T0
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

    Target -= (Target >> 1) & 0x5555555555555555;

    assert(Target == 
	   PowTwo(62) * (T63 + T62) +
	   PowTwo(60) * (T61 + T60) +
	   PowTwo(58) * (T59 + T58) +
	   PowTwo(56) * (T57 + T56) +
	   PowTwo(54) * (T55 + T54) +
	   PowTwo(52) * (T53 + T52) +
	   PowTwo(50) * (T51 + T50) +
	   PowTwo(48) * (T49 + T48) +
	   PowTwo(46) * (T47 + T46) +
	   PowTwo(44) * (T45 + T44) +
	   PowTwo(42) * (T43 + T42) +
	   PowTwo(40) * (T41 + T40) +
	   PowTwo(38) * (T39 + T38) +
	   PowTwo(36) * (T37 + T36) +
	   PowTwo(34) * (T35 + T34) +
	   PowTwo(32) * (T33 + T32) +
	   PowTwo(30) * (T31 + T30) +
	   PowTwo(28) * (T29 + T28) +
	   PowTwo(26) * (T27 + T26) +
	   PowTwo(24) * (T25 + T24) +
	   PowTwo(22) * (T23 + T22) +
	   PowTwo(20) * (T21 + T20) +
	   PowTwo(18) * (T19 + T18) +
	   PowTwo(16) * (T17 + T16) +
	   PowTwo(14) * (T15 + T14) +  
	   PowTwo(12) * (T13 + T12) +
	   PowTwo(10) * (T11 + T10) +  
	   PowTwo(8)  * (T9 + T8) +
	   PowTwo(6)  * (T7 + T6) +  
	   PowTwo(4)  * (T5 + T4) +
           PowTwo(2)  * (T3 + T2) +               
                        T1 + T0
	   );
    
  	//
    // Next, combine the totals in adjacent two-bit fields into a four-bit
    // field.
    //

    Target = (Target & 0x3333333333333333) +
             ((Target >> 2) & 0x3333333333333333);

    assert(Target == 
	   PowTwo(60) * (T63 + T62 + T61 + T60) +
	   PowTwo(56) * (T59 + T58 + T57 + T56) +
	   PowTwo(52) * (T55 + T54 + T53 + T52) +
	   PowTwo(48) * (T51 + T50 + T49 + T48) +
	   PowTwo(44) * (T47 + T46 + T45 + T44) +
	   PowTwo(40) * (T43 + T42 + T41 + T40) +
	   PowTwo(36) * (T39 + T38 + T37 + T36) +
	   PowTwo(32) * (T35 + T34 + T33 + T32) +
	   PowTwo(28) * (T31 + T30 + T29 + T28) +
	   PowTwo(24) * (T27 + T26 + T25 + T24) +
	   PowTwo(20) * (T23 + T22 + T21 + T20) +
	   PowTwo(16) * (T19 + T18 + T17 + T16) +  
	   PowTwo(12) * (T15 + T14 + T13 + T12) +
	   PowTwo(8) * (T11 + T10 +  T9 + T8) +
	   PowTwo(4) * (T7 + T6 + T5 + T4) +
                       T3 + T2 + T1 + T0);


    //
    // Now, combine adjacent four-bit fields to end up with a set of 8-bit
    // totals.
    //

    Target = (Target + (Target >> 4)) & 0x0F0F0F0F0F0F0F0F;

    assert(Target == 
	   PowTwo(56) * (T63 + T62 + T61 + T60 + T59 + T58 + T57 + T56) +
	   PowTwo(48) * (T55 + T54 + T53 + T52 + T51 + T50 + T49 + T48) +
	   PowTwo(40) * (T47 + T46 + T45 + T44 + T43 + T42 + T41 + T40) +
	   PowTwo(32) * (T39 + T38 + T37 + T36 + T35 + T34 + T33 + T32) +
	   PowTwo(24) * (T31 + T30 + T29 + T28 + T27 + T26 + T25 + T24) + 
	   PowTwo(16) * (T23 + T22 + T21 + T20 + T19 + T18 + T17 + T16) +
           PowTwo(8)  * (T15 + T14 + T13 + T12 + T11 + T10 +  T9 + T8)  +
	                 T7 + T6 + T5 + T4 + T3 + T2 + T1 + T0);


    //
    // Finally, sum all of the 8-bit totals.  The result will be the
    // number of bits that were set in Target.
    //

    assert(Target <= 0x0808080808080808);
    
    // for the following, Z3 loops
    // probably does not know that multiplication overflow forgets bits beyond #63
    // (cf. 32 bit version, which verifies immediately)

//     Target = (Target * 0x0101010101010101) >> 56;

//     assert(Target == 
// 	   T63 + T62 + T61 + T60 + T59 + T58 + T57 + T56 +
//            T55 + T54 + T53 + T52 + T51 + T50 + T49 + T48 +
//            T47 + T46 + T45 + T44 + T43 + T42 + T41 + T40 +
//            T39 + T38 + T37 + T36 + T35 + T34 + T33 + T32 +
//            T31 + T30 + T29 + T28 + T27 + T26 + T25 + T24 + 
// 	   T23 + T22 + T21 + T20 + T19 + T18 + T17 + T16 +
// 	   T15 + T14 + T13 + T12 + T11 + T10 +  T9 + T8 +
// 	   T7 + T6 + T5 + T4 + T3 + T2 + T1 + T0);

    return Target;

}
