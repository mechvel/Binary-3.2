Announcement
------------

   Binary-3.2  -- a Pure Binary Natural Number Arithmetic library 
                  for Agda

is available here on GitHub
and on

    http://www.botik.ru/pub/local/Mechveliani/binNat/3.2


Binary-3.2  is a pure, regular-performance, complete, and certified 
            binary arithmetic for natural numbers
            written in Agda.

It has been tested under  Agda 2.5.4, MAlonzo, ghc-7.10.2.



`Pure'  
means that Binary-3.2 never uses a built-in arithmetic (on Nat) to 
essentially change performance.
The performance order is supposed to remain with replacing the Nat 
arithmetic with the naive unary arithmetic.

`Regular performance' 
means that the arithmetic on Bin of Binary-3.2 has a 
regular performance cost order -- the one expected for the corresponding 
known naive operations with bit lists.
At least this holds for  <-cmp, _+_, _-._, _*_, _divMod_, _gcd_.
Examples:
*  The comparison  <-cmp x y  on Bin costs  O(|x| + |y|),  
                                            where  |z| = bitLength z.

*  Division with remainder  divMod x y y≢0  on Bin is implemented as a loop 
   of  {s = shift n dr  for certain n;  dd := dd -. s}  repeated O(|x|) times. 
   So that it costs  O( |x|^2 ).

`Complete'  
means that all the items are implemented that are usually 
required for standard arithmetic. There are provided the following items.

*  DecTotalOrder instance for Bin,
                 for  x <= y  defined on Bin as   x < y or x == y.
*  StrictTotalOrder instance for Bin, _<_.
*  The bijection property for the map pair  toNat, fromNat. 
*  Subtraction _-._ on Bin,  with the needed properties proved.
*  The proofs for isomorphism for _+_, _*_, _-._  for toNat, fromNat.
*  The monotonicity proofs for  toNat, fromNat  for _<=_ and Nat._<=_.
   A similar monotonicity for _<_ and Nat._<=_ are proved.
*  Various kinds of monotonicity for  _+_, _*_, _-._   for _<=_ and _<_  
   are proved.
*  The  CommutativeSemiring  instance  for Bin.
*  Division with remainder  and  GCD   for Bin.
*  The demonstration/test programs for  divMod and gcd.


`Certified'  means that everything is proved in Agda which is regularly 
             required of the above operations.


Usage of Standard library
-------------------------

Bin0.agda  _copies_ the following items from  Data.Bin of Standard library:

  Bin⁺,    data Bin,   2^_,        toBits,   ⌊log₂_⌋,    _*2,  
  _*2+1,   ⌊_/2⌋,      Carry,      addBits,  addCarry,   _+_,
  _*_,     fromBits,   addBitList, 

The last three have a slight change in implementation.

Nothing else about Bin is taken from Standard library.

The definition for inequalities on Bin is totally changed in Bin0, Bin1.


More detailed explanations are given in  README.agda.


Binary-3.2  has been tested under  Agda 2.5.4, MAlozo, ghc-7.10.2

It also includes the module  LtReasoning.agda  -- a support for inequality 
reasoning by Ulf Norell.

Installation: 

              agda -c $agdaLibOpt GCDTest.agda


Comments and improvements are welcome.

---------------------
Sergei D. Meshveliani
mechvel@botik.ru
