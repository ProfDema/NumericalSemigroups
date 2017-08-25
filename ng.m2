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
    result := new List from {};
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
    result = append(result, {0,1});
    return result
)

cmpLead = method()
cmpLead(List, List) := (L1, L2) -> (
    result := false;
    lastL1Item = L1#(#L1-1);
    lastL2Item = L2#(#L2-1);
    if lastL1Item >= lastL2Item then (
       result = true;
       ix := 0;
       while ix < #L1 - 1 and result do (
	   if L1#ix < lastL2Item then result = member(L1#ix, L2);
	   ix = ix + 1;
       );
    );
    return result
)

ringChains=method()
ringChains(NumericalSemigroup) := nsg -> (
    psr := generatePSR nsg;
    pst = poset(psr, cmpLead);
    chn = chains pst;
    chns = new List from {};
    for lst in chn do
        if #lst > 1 then
           if lst#0 == psr#0 and #lst > 2 and lst#(#lst-1) == {0,1} then 
	      chns = append(chns, lst);
    return chns
)  
end--
restart
load "ng.m2"
L = new List from {3,7,8}
n1 = new NumericalSemigroup from numericalSemigroup L
showNSG n1
g2 = generatePSR n1
r = ringChains n1
n2 = new NumericalSemigroup from numericalSemigroup {3,4,5}
r2 = ringChains n2
restart
R = ZZ/101[x,y,z, Degrees=>{3,4,5}]
--(R1, f1) = selectVariables({0,1,2},R)
--describe R1
--(R2, f2) = selectVariables({3},R)
--describe R2
--(R3, f3) = selectVariables({4}, R)
--describe R3
--random(6,R) --random element of 6 degree
--(R4, f4) = selectVariables({1}, R)
--MR1 = module R1
--MR4 = module R4
-- P1 = MR1 ++ MR4 ++ MR4 ->no common ring
--describe MR1
-- m1 = matrix {{vars R1, vars R4, vars R4}} -> no common ring
I1=ideal(y*y-x*z,y*z-x^3,z^2-x^2*y)
R1 = R/I1 --R1 looks like k[t^3,t^4,t^5]
vars R1
peek vars R1
