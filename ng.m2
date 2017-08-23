NumericalSemigroup = new Type of MutableHashTable
numericalSemigroup = method()
numericalSemigroup(List):= numsgGens -> (
    nsg := new MutableHashTable;
    result = computeFrobenius numsgGens;
    nsg#"frobNum" = result#0;
    nsg#"gaps" = result#1;
    nsg#"lead" = result#2;
    return nsg)

frobeniusNumber = method()
frobeniusNumber(NumericalSemigroup) := nsg -> nsg#"frobNum"

gaps = method()
gaps(NumericalSemigroup) := nsg -> nsg#"gaps"

lead = method()
lead(NumericalSemigroup) := nsg -> nsg#"lead"

showNSG = method()
showNSG(NumericalSemigroup) := nsg -> (
   fb = toString frobeniusNumber nsg;
   fb = concatenate("Frobenius number: ", fb, "\nGaps: ");
   gp = sort new List from gaps nsg;
   for ix from 0 to #gp-1 do (
      fb = if (ix < #gp-1) then concatenate(fb, toString gp#ix, ",")  else concatenate(fb, toString gp#ix, "\n");
   );
   return net fb
)

-- Private methods
computeFrobenius = method()
--**********************************************************
--The following method implements Greenberg's algorithm:
--An Algorithm for a Linear Diophantine Equation
--and a Problem of Frobenius
--Published on:
--Numerische Mathematik 34, 349-352 (1980)
--**********************************************************
computeFrobenius(List) := (generators) -> (
   -- cleanup
   ngen := #generators;
   gen1 := generators#0;
   A := new MutableList from {0,gen1};
   for i from 1 to ngen-1 do (
      geni := generators#i;
      if geni%gen1 =!= 0 then (
	  print geni;
	 elim := false;
         for j from 1 to i-1 do (
	     if (geni-generators#j)%gen1 == 0 then elim = true;
	 );
         if not elim then A = append(A, geni);
      );
   );
   A' := new MutableList from {};
   D := new MutableList from {}; 
   C := new MutableList from {}; 
   E := new MutableList from {}; 
   F := new MutableList from {};
   n := #A-1;
   an := A#n;
   for ix from 0 to an do (
       A'#ix = 0;
       C#ix = 0;
       D#ix = 0;
       E#ix = 0;
       F#ix = 0;
   );
   
   a1 := A#1;
   -- Step 1: Initialize
   for j from 2 to n do (
      a := A#j;
      A'#j = a % a1;
      D#(A'#j) = j;
      C#(A'#j) = j;
      E#j = A'#j;
      F#(A'#j) = a;
   );
   
   m := n;
   j := 2;
   
   --Step 2
   while j <= m do (
      i := E#j; --2b
      if C#i == j then (
         k = 2;
	 while k <= D#i do ( --2c
	   L := F#i + A#k;
	   L' := L % a1;
	   if not ((L' == 0) or (F#L' > 0 and F#L' <= L)) then (
	      m = m + 1;
	      D#L' = k;
	      C#L' = m;
	      E#m = L';
	      F#L' = L;
	   );
           k = k + 1;
	 );
       );
       j = j + 1;  -- 2a
   );
  -- Step 3
   maxF := -1;
   for L from 1 to a1-1 do (
       if F#L > maxF then maxF = F#L;
   );
   for y in F do print y;
   --Frobenius number
   frobenius := maxF - a1;
   --Gaps
   gaps := new MutableList from {};
   for x from 1 to a1-1 do (
      s1 := (F#x-x)//a1;
      s := 1;
      while (s <= s1) do (
	  L := F#x - s*a1;
	  L1 := L-L//a1*a1;
	  x1 := (F#L1-L)//a1;
	  if x1 >= 0 then gaps = append(gaps, L);
	  s = s + 1;
      );
   );
   -- lead
   lead := new MutableList from {0};
   gps = new Sequence from gaps;
   for x from 1 to frobenius+1 do
      if not member(x, gps) then lead = append(lead, x);
   return (frobenius, gaps, lead)
 )


end--
restart
load "ng.m2"
L = new List from {3,7,8}
n1 = new NumericalSemigroup from numericalSemigroup L
frobeniusNumber n1
showNSG n1


