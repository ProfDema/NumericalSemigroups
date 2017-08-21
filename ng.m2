NumericalSemigroup = new Type of MutableHashTable
numericalSemigroup = method()
numericalSemigroup(List):= numsgGens -> (
    nsg := new MutableHashTable;
    result = computeFrobenius numsgGens;
    nsg#"frobNum" = result#0;
    nsg#"gaps" = result#1;
    return nsg)

frobeniusNumber = method()
frobeniusNumber(NumericalSemigroup) := nsg -> nsg#"frobNum"

gaps = method()
gaps(NumericalSemigroup) := nsg -> nsg#"gaps"

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
   D := new MutableList from {}; 
   C := new MutableList from {}; 
   E := new MutableList from {}; 
   F := new MutableList from {};
   n := #generators;
   
   a1 := generators#0;
   
   for j from 1 to n - 1 do (
      a := generators#j;
      aj := a - a // a1 * a1;
	  D#aj = j+1;
	  C#aj = j+1;
	  E#(j+1) = aj;
	  F#aj = a;
   );
   a2 := a1 - 1;
   lenF := #F;
   print lenF;
   for k from 1 to a2 do (
      if k >= lenF then F#k = 0;
      if instance(F#k, Nothing) then F#k = 0;
   );
   
   m := n;
   j := 2;
   while j <= m do (
      i := E#j;
		if instance(C#i, ZZ) then (
			if C#i == j then (
				k := 2;
				while k <= D#i do (
					 val := F#i + generators#(k-1);
					 val1 := val - val // a1 * a1;
					 if not(val1 == 0) and (F#val1 <= 0 or F#val1 > val) then (
						m = m + 1;
						D#val1 = k;
						C#val1 = m;
						E#m = val1;
						F#val1 = val;
					 );
				     k = k + 1;
			    );
		    );
        );
	   j = j + 1;
   );
   result := -1;
   for x in F do (
      if instance(x, ZZ) then (
         if x > result then result = x;
	  );
   );
   frobenius := result-a1;
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
   return (frobenius, gaps)
 )


end--
restart
load "ng.m2"
L = new List from {2,3}
n1 = new NumericalSemigroup from numericalSemigroup L
frobeniusNumber n1
g = gaps n1
for x in g do print x

