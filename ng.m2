loadPackage"Posets"
NumericalSemigroup = new Type of MutableHashTable
numericalSemigroup = method()
numericalSemigroup(List):= numsgGens -> (
    nsg := new MutableHashTable;
    result = computeFrobenius numsgGens;
    nsg#"frobNum" = result#0;
    nsg#"gaps" = result#1;
    nsg#"lead" = result#2;
    nsg#"generators" = numsgGens;
    return nsg)

genSG = method()
genSG(NumericalSemigroup) := nsg -> nsg#"generators"

frobeniusNumber = method()
frobeniusNumber(NumericalSemigroup) := nsg -> nsg#"frobNum"

gaps = method()
gaps(NumericalSemigroup) := nsg -> nsg#"gaps"

lead = method()
lead(NumericalSemigroup) := nsg -> nsg#"lead"

showNSG = method()
showNSG(NumericalSemigroup) := nsg -> (
   fbr = toString frobeniusNumber nsg;
   gp = sort new List from gaps nsg;
   ld = sort new List from lead nsg;
   gns = new List from genSG nsg;
   fb = "Generators: ";
   for ix from 0 to #gns-1 do (
       fb = if (ix < #gns-1) then concatenate(fb, toString gns#ix, ", ") else concatenate(fb, toString gns#ix);
   );
   fb = concatenate(fb, "\nFrobenius : ", fbr, "\nGaps: ");
   for ix from 0 to #gp-1 do (
      fb = if (ix < #gp-1) then concatenate(fb, toString gp#ix, ", ")  else concatenate(fb, toString gp#ix);
   );
   fb = concatenate(fb, "\nLead: ");
   for ix from 0 to #ld-1 do (
       fb = if (ix < #ld-1) then concatenate(fb, toString ld#ix, ", ") else concatenate(fb, toString ld#ix);
   );
   return peek net fb
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

--
reducedGaps=method()
reducedGaps(NumericalSemigroup) := nsg -> (
    L = {};
    for x in gaps nsg do if x =!= 1 then L = append(L,x);
    return L)

generatePSR=method()
generatePSR(NumericalSemigroup) := nsg -> (
    result := new List from {{0,1}};
    rgaps = sort(reducedGaps(nsg), DegreeOrder=>Descending);
    gnrs = new List from genSG nsg;
    for subset in subsets rgaps do (
        g := sort new List from subset | gnrs;
	n := new NumericalSemigroup from numericalSemigroup g;
	ln := new List from lead n;
	--print ln;
	if not member(ln, result) then result = append(result, ln);
	--print result;
    );
    return result
)

cmpLead = method()
cmpLead(List, List) := (L1, L2) -> (
    result := false;
    if #L1 < #L2 then (
	test := true;
	i := 0;
	while i < #L1-1 do (
	     test = test and L1#i == L2#i;
	     i = i + 1;
	);
        result = test and L1#(#L1-1) >= L2#(#L2-1);
    );
    if #L1 == #L2 then (
       i :=0;
       test := true;
       while i < #L1-1 and not result do (
	  test = test and L1#i == L2#i; 
	  i = i +1;
       );
       if test then test = L1#(#L1-1) >= L2#(#L1-1);
       result = test;	
    );
    if #L1 > #L2 then (
       test := true;
       for i from 0 to #L2-1 do
          test = test and L1#i == L2#i;
       result = test;	
    );
    if #L1 < #L2 then result = isSubset(L1, L2);
    return result
)

ringChains=method()
ringChains(NumericalSemigroup) := nsg -> (
    psr := generatePSR nsg;
    pst = poset(psr, cmpLead);
    chn = maximalChains pst;
    return chn
)  
end--
restart
load "ng.m2"
L = new List from {3,7,8}
n1 = new NumericalSemigroup from numericalSemigroup L
showNSG n1
g2 = generatePSR n1
--r = ringChains n1
for i from 0 to #g2-1 do (
    for j from 0 to #g2-1 do (
	if i=!=j then (
	    print concatenate(toString i," and ",toString j);
	    print cmpLead(g2#i,g2#j);
	    print cmpLead(g2#j,g2#i);
	);
    );
)
