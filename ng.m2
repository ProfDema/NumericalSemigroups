NumericalSemigroup = new Type of MutableHashTable
numericalSemigroup = method()
numericalSemigroup(List):= numsgGens -> (
    nsg := new MutableHashTable;
    nsg#"frobNum" = computeFrobenius numsgGens;
    return nsg)

frobeniusNumber = method()
frobeniusNumber(NumericalSemigroup) := nsg -> nsg#"frobNum"

-- Private methods
computeFrobenius = method()
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
   return result-a1
    )


end--
restart
load "ng.m2"
L = new List from {3,5}
n1 = new NumericalSemigroup from numericalSemigroup L
frobeniusNumber n1
