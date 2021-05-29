helpstr:="Collection of functions for calculations about rational maps 
between projective spaces and their base loci

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% invertBirationalMapRS: computes inverse map of birational map via Russo and Simis's algorithm
% *********************
% input: 1) row matrix, representing a birational map P^n-->P^m 
%        2) ideal, representing the image of the map 
% optional argument: checkInverseMap=>Boolean (default true)
% output: row matrix, representing the inverse map   
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% invertMap: computes inverse map of birational map via method in Parametrization
% *********
% input/output: ring maps of polynomial rings 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% baseLocusOfInverseMap: heuristic method to find base locus of inverse of birational map 
% *********************
% input: 1) Z ideal, representing a projective variety in P^N 
%        2) F ring map, representing a rational map F:P^N-->P^n such that the 
%           restriction F|Z:Z-->P^n is a birational map of type (d,2)  
%        3) H list of ideals, representing a sufficiently large list of 
%           sufficiently general linear subspaces of P^N 
% output: ideal, (candidate to be) the ideal of the base locus of the inverse map
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% invertCremona: computes inverse of Cremona transformation via baseLocusOfInverseMap
% *************
% input/output: row matrix
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% degreeOfRationalMap: computes degree of a rational map as the degree of the general fibre
% *******************
% input: row matrix, representing a rational map P^n-->P^m 
% optional argument: Probabilistic=>Boolean (default true) 
%                    with false value always provides correct answer, 
%                    but generally after a long calculation time 
% output: integer, the degree of the rational map   
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% projectiveDeg: computes projective degrees of a rational map
% *************
% input: 1) row matrix F, representing a rational map F:P^n-->P^m 
%        2) ideal I, representing a subvariety X=V(I) of P^n
%        3) integer i, with 0<=i<=dim X
% output: the i-th projective degree of the restriction map F:X-->P^m 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% projectiveDegrees:    (resp. polarClass:)
% *****************            **********    
% input: (F,I) as in 1) and 2) of projectiveDeg (resp.
%        a homogeneous polynomial P)
% output: the list of all projective degrees of F:X-->P^m
%         (resp. of the polar map of P) 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% homogPartOfImage: helps to determine the image of rational maps 
% ****************
% input: 1) ring map, representing a rational map F:P^n-->Z subset P^m 
%        2) positive integer i
% output: list, a basis of H^0(P^m,I_Z(i))
% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% numberConnectedComponents: checks absolute connection
% *************************
% input: homogeneous ideal I of a polynomial ring over a field K
% output: integer, the number of connected components of V(I) 
%         over the algebraic closure of K
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  
% isSmooth: checks smoothness of subschemes of P^n
% ********
% Input: a homogeneous ideal I of a polynomial ring K[x_0,...,x_n], 
%        representing a closed subscheme X=V(I) subset P^n 
% Optional arguments:
%    reduceToChar => Integer (default 0, not prime) 
%                    if the value is a prime number p and the char of K is 0 
%                    then the routine works with I (mod p) instead than I
%    Use          => {M2,Sage,Singular} (default M2) 
%                    if the value is Sage (resp. Singular) then the computation 
%                    is transferred to the software Sage (resp. Singular), i.e. 
%                    the routine creates the Sage (resp. Singular) input code, 
%                    then it runs Sage (resp. Singular) and reads the output 
%    equidimCheck => Boolean (default false) 
%                    if the value is true then the routine first checks if the 
%                    input ideal is equidimensional 
%    outputFile   => Boolean (default false) 
%                    if the value is true then the routine creates a file 
%                    named output.m2/.sage/.singular containing the ideal 
%                    of the singular locus 
%    details      => Boolean (default true) when false, no messages will be displayed
% Output: a boolean value according to the condition of being smooth for 
%         the projective scheme X 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  
% idealOfSingularLocus: (resp. dimOfSingularLocus)
% ********************         ******************
% Input: either ideal I as in isSmooth() or nothing 
% Optional arguments: Use=> as in isSmooth()
% Output: either ideal (resp. dim) of the singular locus of V(I) or last computed
% (Experimental option for idealOfSingularLocus: Strategy=>elimination)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  
"
needs "Parametrization.m2";

isLinearSystemOnProjectiveSpace := {Message => true} >> o -> (F) -> (
T:=try isPolynomialRing ring F and isField coefficientRing ring F and isHomogeneous ideal F and max degrees ideal F == min degrees ideal F and numgens target F == 1 else false;
if o.Message then if not T then <<"Error: expected a row matrix representing a linear system on a projective space over a field"<<endl; 
T
);

isHomogeneousIdeal := {Message => true} >> o -> (I) -> (
T:=try isPolynomialRing ring I and isField coefficientRing ring I and isIdeal I and isHomogeneous I else false;
if o.Message then if not T then <<"Error: expected a homogeneous ideal of a polynomial ring over a field"<<endl; 
T
);

invertBirationalMapRS = {checkInverseMap => true, quiet => false} >> o -> (F,a)  -> ( 
-- Notation as in [Russo, Simis - On Birational Maps and Jacobian Matrices] 
if not isLinearSystemOnProjectiveSpace F then return; 
if not isHomogeneousIdeal a then return;
if not numgens source F == numgens ring a then (<<"Error: expected an ideal representing the image of the rational map"<<endl; return);
n:=numgens ring F-1;
x:=local x;
R:=coefficientRing(ring F)[x_0..x_n];
I:=sub(F,vars R);
S:=ring a;
phi:=syz I;
local q;
for j to numgens source phi-1 list 
if max degrees ideal matrix phi_j == {1} then q=j+1;
phi1:=submatrix(phi,{0..q-1});
RtensorS:=tensor(R,S);
phi1=sub(phi1,RtensorS);
Y:=sub(vars S,RtensorS);
theta:=transpose submatrix(jacobian ideal(Y*phi1),{0..n},);
theta=sub(theta,S);
S':=S/a; theta':=sub(theta,S');
Z:=kernel theta';
basisZ:=mingens Z; 
if numgens source basisZ == 0 then (<<"Error: it has not been possible to determine the inverse map"<<" (dim Z="<<numgens source basisZ<<")"<<endl; return);
g:=sub(basisZ_0,S);
Inv:=transpose matrix(g);
if o.checkInverseMap then if not isInverseMap(F,Inv) then (<<"Error: it has not been possible to determine the inverse map"<<" (dim Z="<<numgens source basisZ<<")"<<endl; return) else if not o.quiet then (<<"The inverse map has been checked!"<<endl);
Inv 
);

invertMap = (F)  -> ( 
R:=target F;
ImInv:=invertBirationalMap(ideal R,matrix F);
S:=source F;
<<"idealImage="<<toString sub(ImInv#1,vars S)<<endl;
map(S,R,transpose sub(ImInv#0,vars S))
);

restrict := (I,L)->(
-- Input: I, ideal/matrix; L, ideal generated by linear forms. 
-- Output: ideal/matrix
if not (isIdeal L and max degrees L == {1} and vars ring I == vars ring L) then (<<"Error: invalid input data"<<endl; return);
R:=ring I;
c0:=local c0;
x0:=local x0;
delVars:={};
while not L==ideal(0_R) list(
c0=leadCoefficient L_0;  
x0=leadMonomial L_0;   
delVars=delVars|{x0};
subs={x0=>sub((c0*x0-L_0)/c0,R)};
L=ideal submatrix'(gens sub(L,subs),{0});
I=sub(I,subs));
newVars:={};
z:=gens R;
test:=local test;
for i to numgens(R)-1 list (
test=true;
for j to #delVars-1 list if z_i==delVars_j then test=false;
if test then newVars=newVars|{z_i});
R':=coefficientRing(R)[newVars];
sub(I,R')
);

baseLocusOfInverseMap = (Z,F,H) ->(
if not (isHomogeneousIdeal(Z,Message=>false) and isLinearSystemOnProjectiveSpace(matrix F,Message=>false) and (try ring Z === target F else false) and (try #H>=1 else false)) then (<<"Error: invalid input data"<<endl; return);
checkH:=true;
try (for i to #H-1 list checkH=checkH and isHomogeneousIdeal(H_i,Message=>false) and ring H_i === ring Z and max degrees H_i == {1}) else false;
if not checkH then (<<"Error: invalid input data"<<endl; return); 
ringPN:=target F;
ringPn:=source F;
t:=#H-1;
rF:=for i to t list restrict(matrix F,H_i);
rZ:=for i to t list sub(restrict(Z,H_i),ring rF_i);
rFZ:=for i to t list map(ring(rF_i)/rZ_i,ringPn,rF_i);
Q:=for i to t list if Z == ideal ringPN then ideal homogPartOfImage(rFZ_i,2) else kernel rFZ_i;
Y:=trim sum Q;
if not (numgens Y == numgens ringPN and max degrees Y == min degrees Y and max degrees Y == {2})
then (<<"Error: it has not been possible to determine the base locus of inverse map"<<endl; return);
Y
);

invertCremona = (F) -> ( 
R:=ring F;
n:=numgens R-1;
H:=for i to n list ideal random(1,R);
G:=gens baseLocusOfInverseMap(ideal R,map(R,R,F),H);
sigma:=Compose(F,G);
Finv:=Compose(G,invertBirationalMapRS(sigma,ideal R,checkInverseMap=>false));
if not isInverseMap(F,Finv) then (<<"Error: it has not been possible to determine the inverse map"<<endl; return) else (<<"The inverse Cremona has been checked!"<<endl);
Finv 
);

ranlinspace := (R,i) -> (
n:=numgens R -1;
if i == n then return ideal R;
L:=trim ideal for j to n-1-i list random(1,R);
return if dim L - 1 == i then L else ranlinspace(R,i);
);

randomPoint := (R) -> (ranlinspace(R,0));

degreeOfRationalMap = {Probabilistic => true} >> o -> (F) -> (
if not isLinearSystemOnProjectiveSpace F then return; 
ringPn:=ring F;
n:=numgens ringPn-1;
m:=numgens source F-1;
if m<n then return 0;
if not o.Probabilistic then (
idFib:=if m==n then symbolicFibre(F,Image=>false) else symbolicFibre(F);
<<"Generic fibre: "; if m==n then <<"ideal of map^(-1) [1" else <<"ideal of map^(-1)map [1"; for i from 1 to n do <<" a_"<<i; <<"]  ="<<endl<<toString(idFib)<<endl;
return degree idFib
);
kk:=coefficientRing ringPn;
y:=local y; 
ringPm:=kk[y_0..y_m];
h:=map(ringPn,ringPm,F); 
p:=randomPoint ringPn;   
local q;
if m == n then q=sub(p,vars ringPm) else q=preimage(h,p);
idealFibre:=saturate(h(q),ideal(F));
degree idealFibre
);

genericRestriction := (F,I) -> (
R:=ring I;
K:=coefficientRing R;
n:=numgens R - 1;
x:=local x;
R':=K[x_0..x_n];
H:=sub(random(1,R'),x_n=>0);
S:=K[x_0..x_(n-1)];
I':=sub(sub(sub(I,vars R'),x_n=>H),S);
F':=sub(sub(sub(F,vars R'),x_n=>H),S);
(F',I')
);

genericRestrictionOfPolynomial := (P) -> (
R:=ring P;
K:=coefficientRing R;
n:=numgens R - 1;
x:=local x;
R':=K[x_0..x_n];
H:=sub(random(1,R'),x_n=>0);
S:=K[x_0..x_(n-1)];
sub(sub(sub(P,vars R'),x_n=>H),S)
);

projectiveDeg = {dimSubVar => -1} >> o -> (F,I,i) -> (
R:=ring F;
K:=coefficientRing R;
m:=numgens source F-1;
y:=local y;
S:=K[y_0..y_m];
k:=if o.dimSubVar >=0 then o.dimSubVar else dim I -1;
L:=ranlinspace(S,m-k+i);
h:=map(R/I,S,F); 
pi:=map(R/I,R);
Z:=saturate(h(L),pi(ideal F),MinimalGenerators=>true);
di:= if dim Z == i+1 then degree Z else 0;
di
);

projectiveDegrees = (F,I) -> (
if I === null then I=ideal ring F;
k:=dim I - 1;
Degs:={projectiveDeg(F,I,0,dimSubVar=>k)};
for i from 1 to k do (
(F,I)=genericRestriction(F,I);
Degs=Degs|{projectiveDeg(F,I,0,dimSubVar=>(k-i))});
Degs
);

polarClass = (P) -> (
Degs:={projectiveDeg(transpose jacobian ideal P,ideal ring P,0)};
for i from 1 to numgens ring P -1 do (
P=genericRestrictionOfPolynomial P;
Degs=Degs|{projectiveDeg(transpose jacobian ideal P,ideal ring P,0)});
Degs
);

homogPartOfImage = (phi,d) -> (  
R:=target phi; 
kk:=coefficientRing R;
m:=numgens R-1;
n:=numgens source phi-1;
N:=binomial(n+d,n)-1;
a:=local a; A:=kk[a_0..a_N];
t:=local t; S:=A[t_0..t_m];
F:=sub(matrix phi,vars(S));
y:=local y; T:=A[y_0..y_n];
ST=tensor(S,T);
allMons:=gens(ideal(y_0..y_n))^d;
GenPol:=(gens(ideal(a_0..a_N))*transpose(allMons))_(0,0);
subGenPol:=GenPol;
for i to n list subGenPol=sub(subGenPol,y_i=>sub(F_(0,i),ST)); 
subGenPol=sub(subGenPol,S);
Eqs:=sub((coefficients subGenPol)#1,A);
Eqs=transpose gens trim ideal Eqs; 
-- <<"Size lin. sys. matrix: "<<numgens target Eqs<<"x"<<N+1<<endl;
coeffMatrix:=matrix(for i to numgens target Eqs-1 list 
                    for j to N list coefficient(a_j,Eqs_(i,0)));
solutions:=mingens kernel coeffMatrix;
dimension:=numgens source solutions;
Basis:={};
for j to dimension-1 list (
pol_j=sub(GenPol,T);
for i to N list pol_j=sub(pol_j,a_i=>solutions_(i,j));
Basis=Basis|{sub(pol_j,vars(source phi))});
Basis
);

Kernel = (phi,d) -> (trim ideal homogPartOfImage(phi,d)); 

sectionalGenus = (I) -> (
if not isHomogeneousIdeal I then return; 
c:=dim I-2;
if c<0 then (<<"Error: expected ideal of a positive dimensional scheme"<<endl; return);
P:=hilbertPol(I,c);
t:=gens ring P;
sub(1-sub(P,{t_0=>0}),ZZ)
);

numberConnectedComponents = (I) -> (
if not isHomogeneousIdeal I then return; 
X:=Proj(ring(I)/I);
rank HH^0(OO_X)
);

idealofsingularlocus' := (I) -> ( 
-- Experimental --
R:=ring I;
K:=coefficientRing R;
n:=numgens R-1;
m:=numgens I-1;
c:=codim I;
t:=local t;
x:=local x;
a:=min(n+1,m+1);
b:=min(n+2-c,m+2-c);
S:=K[t_1..t_(a*b),x_0..x_n,MonomialOrder=>Eliminate (a*b)];
J:=(map(S,R,{x_0..x_n}))(jacobian I);
if n<m then J=transpose J;
T:=genericMatrix(S,a,b);
C:=saturate(ideal(J*T),minors(b,T));
trim (I+sub(sub(ideal selectInSubring(1,gens gb C),K[x_0..x_n]),vars R))
);
-- -- Example of a connected, pure, 1-dimensional, non-reduced scheme s.t. idealofsingularlocus' yields a different singular scheme 
-- QQ[t,x,y,z]; hankel3=-z^3+2*y*z*t-x*t^2; steiner=x^2*y^2+x^2*z^2+y^2*z^2-2*x*y*z*t; X=ideal(hankel3,steiner);
-- compareSingularLoci X 
compareSingularLoci = (X) -> (
<<"Minors (S1):       "; print(time S1:=idealOfSingularLocus X;);
<<"Elimination (S2):  "; print(time S2:=idealOfSingularLocus(X,Strategy=>elimination););
<<"codim S1                   "<<codim S1<<endl;
<<"numgens S1                 "<<numgens S1<<endl;
<<"S1==S2                     "<<S1==S2<<endl;
<<"saturate(S1)==saturate(S2) "<<saturate(S1)==saturate(S2)<<endl;
<<"radical(S1)==radical(S2)   "<<radical(S1)==radical(S2)<<endl;
);
IDEALOFSINGULARLOCUS:=ideal();
DIMOFSINGULARLOCUS:=infinity;
INPUTIDEAL:=ideal();
INFOSINGULARLOCUS := {Use => M2} >> o -> (I) -> (
if I===INPUTIDEAL then return;
if o.Use == M2 then (isSmooth(I,details=>false); return;);
R:=ring I;
n:=numgens R-1;
x:=local x;
K:=coefficientRing R;
S:=K[x_0..x_n];
I':=sub(I,vars S);
isSmooth(I',Use=>o.Use,equidimCheck=>false,outputFile=>true,details=>false);
fileName:="output.m2";
if o.Use == Singular then fileName="output.singular" else if o.Use == Sage then fileName="output.sage";
str:= "x:=local x; local SingularLocus; local dimSingularLocus;\n" | toExternalString(K) | "[x_0..x_" | toString(n) | "];\n" | get(fileName) | "\n(dimSingularLocus,SingularLocus)";
Out:=value str;
run "rm -f output.m2 output.sage output.singular";
OutId:=if Out_1 =!= ideal(1) then trim sub(Out_1,vars R) else ideal(1_R);
DIMOFSINGULARLOCUS=Out_0;
IDEALOFSINGULARLOCUS=OutId;
INPUTIDEAL=I;
);
idealOfSingularLocus = {Use => M2, Strategy => Minors} >> o -> I -> ( 
if o.Strategy == elimination then if o.Use =!= M2 then (<<"Error: option Use not available with option Strategy"<<endl; return;) else return idealofsingularlocus' I;
I=sequence I;
if #I==0 then return IDEALOFSINGULARLOCUS;
if #I==1 then if I_0 === INPUTIDEAL then return IDEALOFSINGULARLOCUS else (INFOSINGULARLOCUS(I_0,Use=>o.Use); return idealOfSingularLocus());
);
dimOfSingularLocus = {Use => M2} >> o -> I -> (
I=sequence I;
if #I==0 then return DIMOFSINGULARLOCUS;
if #I==1 then if I_0 === INPUTIDEAL then return DIMOFSINGULARLOCUS else (INFOSINGULARLOCUS(I_0,Use=>o.Use); return dimOfSingularLocus());
);

isSmooth = {reduceToChar => 0, Use => M2, equidimCheck => false, outputFile=>false, details => true} >> o -> (I) -> ( 
if not isHomogeneousIdeal I then return; 
if o.equidimCheck then if not isEquidimensional I then (if o.details then <<"Error: expected an equidimensional ideal"<<endl; return false;);
R:=ring I;
if I==ideal(1_R) then return true;
K:=coefficientRing R;
n:=numgens R-1;
c:=codim I;
c':=c; local dimSingularLocus; local u;
charReduced:=false;
if isPrime o.reduceToChar and char K == 0 then ( 
if o.details then <<"Reducing to characteristic "<<o.reduceToChar<<"..."<<endl;
K=ZZ/(o.reduceToChar);
x:=local x;
R=K[x_0..x_n];
I=sub(I,vars R);
c'=codim I;
if (c' =!= c and o.details) then <<"Warning: codim(input subscheme)="<<c<<" but codim(input subscheme mod "<<o.reduceToChar<<")="<<c'<<endl; 
charReduced=true);  
if o.Use==Singular then (
if o.details then <<"Running Singular..."<<endl;
fromM2toSingular I;
run "Singular -qc 'execute(read(\"input.singular\"));'";
singularOutput:=get "output.singular";
u=regex("dimSingularLocus=\n",singularOutput);
dimSingularLocus=value substring(singularOutput, u_0_0+u_0_1);
run "rm input.singular")
else if o.Use==Sage then (
if o.details then <<"Running Sage..."<<endl;
fromM2toSage I;
run "sage input.sage";
sageOutput:=get "output.sage";
u=regex("dimSingularLocus= ",sageOutput);
dimSingularLocus=value substring(sageOutput, u_0_0+u_0_1);
run "rm input.sage input.sage.py")
else (
SingularLocus:=trim(minors(c',jacobian I)+I);
dimSingularLocus=dim SingularLocus -1;
IDEALOFSINGULARLOCUS=SingularLocus;
DIMOFSINGULARLOCUS=dimSingularLocus;
INPUTIDEAL=I;
if o.outputFile then (
F := openOut "output.m2"; 
F << "SingularLocus="<<toString SingularLocus<<";"<<endl;
F << "dimSingularLocus= "<<dimSingularLocus;
close F));
smoothness:=dimSingularLocus <= -1;
if charReduced and (not smoothness or c'=!=c) and o.details then <<"Warning: the answer may not be the same in characteristic 0"<<endl;
if dimSingularLocus >= 0 and not charReduced and o.details then <<"Dimension of the singular locus: "<<dimSingularLocus<<endl;
if not o.outputFile then run "rm -f output.m2 output.singular output.sage"; -- this also removes old output files!
smoothness
);

isInverseMap = (F,G) -> (
if numgens source F =!= numgens ring G or numgens ring F =!= numgens source G then return false;
ringOfSource:=ring F;
ringOfTarget:=ring G;
mapF:=map(ringOfSource,ringOfTarget,F);
mapG:=map(ringOfTarget,ringOfSource,G);
Composition:=matrix(mapF*mapG);
fixedComponent:=sub(Composition_(0,0)/(vars(ringOfSource))_(0,0),ringOfSource);
identityOfSource:=fixedComponent*matrix(vars(ringOfSource));
identityOfSource==Composition
);

Compose = (F,G) -> (
if numgens source F =!= numgens ring G then (<<"Error: maps not composable"; return);
R:=ring F;
K:=coefficientRing R;
S:=ring G;
N:=numgens source G-1;
t:=local t;
T:=K[t_0..t_N];
mapF:=map(R,S,F);
mapG:=map(S,T,G);
Comp:=(for i to N list (matrix(mapF*mapG))_(0,i));
sub(matrix({Comp/gcd(Comp)}),R)
);

hilbertPol = (I,c) -> (
-- Hilbert polynomial of general linear sections.
-- c is the codimension of the linear space L intersecting V(I).
-- In particular, hilbertPol(I,0) is the Hilbert polynomial of V(I).
t:=local t;
R:=QQ[t];
P:=sub(hilbertPolynomial(I,Projective=>false),vars R);
for i to c-1 list P=P-sub(P,{t=>t-1});
P
);

symbolicFibre = {Image => true} >> o -> (F) -> ( 
-- Input: F row matrix, representing a rational map F:P^n-->P^m
-- Optional argument: Image=>Boolean (default is true)
-- Output: the ideal of closure(F^(-1)F(p)) (resp. of closure(F^(-1)(p)) if option Image is false and P^n=P^m), where p=[1,a_1,...,a_n]\in P^n  
n:=numgens ring F-1;
m:=numgens source F-1;
K:=coefficientRing ring F;
a:=local a;
A:=frac(K[a_1..a_n]);
ringPn:=A[gens ring F];
x:=gens ringPn;
F=sub(F,ringPn);
y:=local y; 
ringPm:=A[y_0..y_m];
h:=map(ringPn,ringPm,F);
p:=ideal(for i from 1 to n list a_i*x_0-x_i);
local q;
if not o.Image and m==n then q=sub(p,vars ringPm) else q=preimage(h,p); 
idealFibre:=saturate(h(q),ideal(F));
idealFibre
);

isEquidimensional = (I) -> (
I=saturate I;
topComponents I == I
);

fromM2toSingular = (I) -> ( 
-- Create the Singular code to compute the singular locus of the projective scheme defined by I.
R:=ring I;
n:=numgens R-1;
m:=numgens I-1;
ch:=char coefficientRing R;
x:=gens R;
cod:=codim I; 
F:=openOut "input.singular";
F<<"ring R="<<ch<<",("<<toString(x_0);
for i from 1 to n do F<<","<<toString(x_i);
F<<"),dp;"<<endl<<"ideal I="<<toString(I_0);
for i from 1 to m do F<<","<<toString(I_i);
F<<";"<<endl<<"matrix J=jacob(I);"<<endl;
F<<"ideal M=minor(J,"<<toString(cod);
F<<");"<<endl<<"ideal S=M+I;"<<endl<<"S=std(S);"<<endl<<"int a=dim(S);"<<endl;
F<<"write(\":w output.singular\",\"SingularLocus=ideal(\",S,\");   \",\"dimSingularLocus=\",a-1);"<<endl<<"exit;";
close F;
);

fromM2toSage = (I) -> ( 
-- Create the Sage code to compute the singular locus of the projective scheme defined by I.
K:=coefficientRing ring I;
x:=gens ring I;
n:=#x-1;
m:=numgens I-1;
F := openOut "input.sage"; 
F << "n="<<n<<";\n";
if char(K)==0 then (F<<"K=QQ;\n") else (F<<"K=GF("<<char(K)<<");\n");
F << "PP=ProjectiveSpace(n,K,'";
for i to n-1 do (F << toString(x_i) <<",");
F << toString(x_n) << "');\n"; 
F << "PP.inject_variables();\n";
F << "eqs=["<<toString I_0;
for i from 1 to m-1 list (F <<",\n    " << toString I_i);
if m>0 then (F <<",\n     " << toString I_m <<"];\n") else (F <<"];\n"); 
F << "varsPP=[ ";
for i to n-1 list (F << toString(x_i) <<", ");
F << toString x_n <<" ];\n";
F << "X=PP.subscheme(eqs);\n";
F << "I=jacobian(eqs,varsPP);\n";
F << "minorsI=I.minors(X.codimension());\n";
F << "SingularLocus=X.intersection(PP.subscheme(minorsI));\n";
F << "idealSingularLocus=SingularLocus.defining_polynomials();\n";
F << "f = file('output.sage','w');\n";
F << "f.write(str('SingularLocus=ideal'));\n";
F << "f.write(str(idealSingularLocus));\n";
F << "f.write(str(';\\ndimSingularLocus= '));\n";
F << "f.write(str(SingularLocus.dimension()));\n";
F << "f.close();\n";
F << "exit\n";
close F; 
);

helpbir = () -> (
<<helpstr<<endl;
);  

starting := () -> (
<<"loaded bir.m2 (v. 11-06-2015), see main available functions by helpbir()\n";  
);  

starting() 
