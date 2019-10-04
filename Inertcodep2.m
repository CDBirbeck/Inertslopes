
SetMemoryLimit(1*10^11);

SetSeed(2472118994,6863);


/*This is code to compute slopes in the case where p=2, your field is Q(\sqrt 5) and the level is U_0(p^2).  */
/*To run the code, whan you want do is run the code UpMatrix, this takes as input the precision at which you want to work with, i.e. what
precision the matrices entries will have.
Once you run this, the output will be a function, call it Up. This function Up takes 3 inputs, first are k_1,k_2 which are the weight of
modular forms you want. So give it odd positive integers, since those are all the weights in this case, the last argument is for how big
you want the matrix to be. Since this computes overconvergent forms our Up matrices are truncations of the infinite diml matrix, so this 
last argument controls the size of the truncation. By default it also uses the basis as described in the paper "2-adic slopes of Hilbert modular forms over Q(sqrt 5)".  */


/* There is also a function Brantmatrices, will return the matrices used to define the Up operator at level U_0(p^2). 
Specifially, the matrices in Proposition 2.7 of loc.cit.*/




P<x> := PolynomialRing(Integers());
 F:=NumberField(x^2-5);

Foo:= InfinitePlaces(F);
Z:=RingOfIntegers(F);
A1:= QuaternionAlgebra(ideal<Z | 1>, Foo[1..2]);
AO:=MaximalOrder(A1);

delete AO`pMatrixRings;
delete AO`pMatrixRings;
delete AO`pMatrixRings;
NN2:=Units(AO);
N,b:=NormOneGroup(AO);
N2:=[b(n):n in N];


OOrder:=function(O,N,P)
 
	Z_F := BaseRing(O);
	 
	bns:=[];
	  for pp in Factorization(N) do
	    PO := PseudoBasis(O);
	    M2Fp, phi, m := pMatrixRing(O, pp[1]:Precision:=P);
	    S := [MatrixUnit(M2Fp, i, j)@@phi : i,j in [1..2]]
	         cat [PO[i][2] : i in [1..4]];
	    I := [ideal<Z_F | 1>, ideal<Z_F | 1>, pp[1]^pp[2], ideal<Z_F | 1>]
	         cat [pp[1]^pp[2]*PO[i][1] : i in [1..4]];
	    O := Order(S, I);
		bns:=bns cat [phi];
	  end for;

	  O`IsEichler := [* true, O!1 *];
	  return O, bns;
	end function;




I:=function(F,n)
	Z:=RingOfIntegers(F);
	return ideal<Z|n>;
	end function;

pq:=function(F,n)
	Z_F:=RingOfIntegers(F);
	if IsPrime(n) then
	return Decomposition(Z_F,n)[1][1];
	else return ideal<Z_F|n>;
	end if;
	end function;


N1:=function(F,p)
	/*The Image of the norm one elements under Residuematrixring*/
	x,y:=ResidueMatrixRing(AO,p);
	return [y(n): n in N2];
	end function;


orbit:=function(PP1,OS2)
	return [x : x in PP1 | x in OS2];
	end function;


ok:=function(i,N)
	return [x*i : x in N];
	end function;

OR:=function(N,Q,T,li)
	ans:=[]; 
	bns:=[];
	i:=0; 
	while i ne #Q do
	i:=i+1;
	 if Q[i] in ans then
	 ans:=ans cat [];
	else
	 ans:=ans cat [x : x in ok(Q[i],N) | x in Q];
	 bns:=bns cat [[y: y in [x : x in ok(Q[i],N) | x in Q] | Valuation(T(y)[2][1]) gt 0][li]];
	end if;
	end while; 
	return SequenceToSet(bns);
	end function;




OR2:=function(N,Q)
	ans:=[]; 
	bns:=[];
	i:=0; 
	while i ne #Q do
	i:=i+1;
	 if Q[i] in ans then
	 ans:=ans cat [];
	else
	 ans:=ans cat [x : x in ok(Q[i],N) | x in Q];
	 bns:=bns cat [ [x : x in ok(Q[i],N) | x in Q][1]];
	end if;
	end while; 
	return SequenceToSet(bns);
	end function;






Norm_p_elements2:=function(F,QQ,n)
	r:=Trace(F!n);
	E:=Enumerate(QQ,r,r);
	En:=[x : x in E | Norm(x) eq n];
	return OR2(N2,En);
	end function;


Por1:=function(F,p)
		/*This is the same as ProjOrb, but insted of givin stabilisers it gives the map that comes with ProjectiveLine*/
		Z:=RingOfIntegers(F);
		N:=N1(F,p);
		PS1,f11:=ProjectiveLine(quo<Z|p>:Type:="Matrix");
		  f2:=function(x)
		  a,b,c:=f11(x,false,false);
		  return b;
		  end function;
		ook:=function(i,N)
		return [f2(x*i) : x in N];
		end function;

		ans:=[];
		bns:=[];
		i:=0;
		while SequenceToSet(ans) ne PS1 do
		i:=i+1;
		ans:=ans cat orbit(PS1,ook(PS1[i],N));
		bns:=bns cat [orbit(PS1,ook(PS1[i],N))];
		end while;
		return SetToSequence(SequenceToSet([bns[i][1] : i in [1..#bns]])),f11;
		end function;


		Porlift:=function(F,c,cc)

		P:=Por1(F,c);
		primes:=Factorization(cc);

		In:=function(x);
		if x eq 0 then
		 return x;
		 else 
		 return 1/x;
		end if;
		end function;


		ans:=[* *];

		for p in primes do

		if IsSplit(p[1]) then

		q,j:=quo<Z|p[1]^p[2]>;
		red:=[[q!pp[1][1],q!pp[2][1]]: pp in P];
		redi:=[[In(q!pp[1][1]),In(q!pp[2][1])]: pp in P];	
		redu:=[[Eltseq(D[1])[1],Eltseq(D[2])[1]]: D in red];
		redui:=[[Eltseq(D[1])[1],Eltseq(D[2])[1]]: D in redi];
		bns:=[];	
			for i in [1..#redu] do
			if redu[i][1] ne 0 then
			bns:=bns cat [[redu[i][1],0,redu[i][2],redui[i][1]]];
			else 
			bns:=bns cat [[redu[i][1],redui[i][2],redu[i][2],0]];
			end if;
			end for;
		Ma:=[* Matrix(pAdicField(Completion(F,p[1]:Precision:=300)),2,2,bb) : bb in bns *];
		ans:=ans cat [* Ma *];

		elif IsInert(p[1]) then 
		q,j:=quo<Z|p[1]^p[2]>;
		red:=[[q!pp[1][1],q!pp[2][1]]: pp in P];
		redi:=[[In(q!pp[1][1]),In(q!pp[2][1])]: pp in P];	
		C,kr:=Completion(F,p[1]:Precision:=300);
		redu:=[[C! kr(F! Eltseq(D[1])),C! kr(F! Eltseq(D[2]))]: D in red];
		redui:=[[In(C! kr(F! Eltseq(D[1]))),In(C! kr(F! Eltseq(D[2])))]: D in red];

		bns:=[];	
			for i in [1..#redu] do
			if redu[i][1] ne 0 then
			bns:=bns cat [[redu[i][1],0,redu[i][2],redui[i][1]]];
			else 
			bns:=bns cat [[redu[i][1],redui[i][2],redu[i][2],0]];
			end if;
			end for;
		Ma:=[* Matrix(C,2,2,bb) : bb in bns *];
		ans:=ans cat [* Ma *];

		else 
		return "PLEASE NOT A RAMIFIED PRIME";

		end if;




		end for;

		cns:=[* *];

		for j in [1..#P] do
		cns:=cns cat [* [* ans[i][j]: i in [1..#primes]*] *];
		end for;

		return cns,ans;


		end function;



ProjOrbits2:=function(F,p)
	/*This gives the projective orbits as first output and the stabilizers as the second.*/ 
	Z:=RingOfIntegers(F);
	x,y:=ResidueMatrixRing(AO,p);
	PS1,f1:=ProjectiveLine(quo<Z|p>: Type:="Matrix");
		  f2:=function(x)
		  a,b,c:=f1(x,false,false);
		  return b;
	end function;

	ook:=function(i,N)
	return [f2(y(x)*i) : x in N2];
	end function;

	ans:=[];
	bns:=[];
	i:=0;
	while SequenceToSet(ans) ne PS1 do
	i:=i+1;
	ans:=ans cat orbit(PS1,ook(PS1[i],N));
	bns:=bns cat [orbit(PS1,ook(PS1[i],N))];
	end while;
	C:= SetToSequence(SequenceToSet([bns[i][1] : i in [1..#bns]]));


	dn:=[];
	for i in C do
		   g:=[u : u in N2 | f2(y(u)*i) eq i];
		   dn:=dn cat g;
	end for;

	return C,f1,dn;

	end function;


ProjOrbitsss:=function(F,p)
	/*This gives the projective orbits as first output and the stabilizers as the second.*/ 
	Z:=RingOfIntegers(F);
	x,y:=ResidueMatrixRing(AO,p);
	PS1,f1:=ProjectiveLine(quo<Z|p>: Type:="Matrix");
		  f2:=function(x)
		  a,b,c:=f1(x,false,false);
		  return b;
	end function;

	ook:=function(i,N)
	return [f2(y(x)*i) : x in N2];
	end function;

	ans:=[];
	bns:=[];
	i:=0;
	while SequenceToSet(ans) ne PS1 do
	i:=i+1;
	ans:=ans cat orbit(PS1,ook(PS1[i],N));
	bns:=bns cat [orbit(PS1,ook(PS1[i],N))];
	end while;
	C:= SetToSequence(SequenceToSet([bns[i][1] : i in [1..#bns]]));


	dn:=[];
	for i in C do
		   g:=[u : u in N2 | f2(y(u)*i) eq i];
		   dn:=dn cat g;
	end for;

	return C,f1,dn;

	end function;



	Norm_p_elements:=function(F,Q,n,T,li)
	r:=Trace(F!n);
	E:=Enumerate(Q,r,r);
	En:=[x : x in E | Norm(x) eq n];
	return OR(N2,En,T,li);
	end function;

Projlift:=function(F,c,f,pres);
	P,ak,bk:=ProjOrbitsss(F,c);
	q:=quo<Z|c>;
	ans:=[];

	for p in P do
	a:=q! p[1][1];
	b:=q! p[2][1];
	E:=exists(t){[c,d]: c in q, d in q | a*d-b*c eq q!1};
	cc:=t[1];
	dd:=t[2];
	ans:= ans cat [Matrix(q,2,2,[a,cc,b,dd])];
	end for;

	primes:=Factorization(c);




	matlifts:=function(M,kr,p,pr)

	_,iso:=IsIsomorphic(Domain(kr),F);
	if IsSplit(pr) then
	q:=quo<Z|p>;
	MM:=ChangeRing(M,q);
	E:=Eltseq(MM);
	K:=Codomain(kr);
	EL:=[kr(F! Eltseq(e)) : e in E];
	return Matrix(K,2,2,EL);
	else
	q:=quo<Z|p>;
	MM:=ChangeRing(M,q);
	E:=Eltseq(MM);
	K:=Codomain(kr);
	P<x>:=PolynomialRing(K);
	un:=Roots(P! f)[1][1];

	 lif:=function(v)
	 return K! v[1]+K! un*v[2];
	 end function;
	EL:=[kr(iso(Z! q! e)) : e in E];
	
	mr:=Matrix(K,2,2,EL);
	dr:=Determinant(mr);
	mr[1][1]:=mr[1][1]/dr;
	mr[1][2]:=mr[1][2]/dr;
	return mr;
	end if;

	end function;

	bns:=[* *];
	cns:=[];
	dns:=[];

	for p in primes do
	_,T,k:=pMatrixRing(A1,p[1]: Precision:=pres); /*This is where the AO,A1 thing is since pMatrixRings is slightly broken*/
	E:=[* matlifts(a,k,p[1]^p[2],p[1]): a in ans *];
	bns:=bns cat [* E *];
	cns:=cns cat [T];
	dns:=dns cat [k];
	end for;




	ens:=[* *];

	for j in [1..#P] do
	ens:=ens cat [* [* bns[i][j]: i in [1..#primes]*] *];
	end for;



	return ens,cns,dns,primes,ak,bk; 	





	end function;




f:=function(i,j)
	return (i+j+1)*(i+j)/2+j;
	end function;

EP:=function(j,i);
	m:=Maximum([i,j]);
	if i ne m then
	 return j^2+i;
	else return i^2+i+j;
	end if;
	end function;


FII:=function(n)
	C:=[[i,j]: i,j in [0..n]| f(i,j) eq n];
	return C[1];
	end function;


fi:=function(n);
	i:=Floor((-1+Sqrt(1+8*n))/2);
	return [Integers()! ((i*(3+i)/2)-n), Integers()! (n-(i*(i+1)/2))];
	end function;

EPi:=function(n)

	a:=Floor(Sqrt(n));
	if n-a^2 lt a then 
	return [a,n-a^2];
	else return [n-a^2-a,a];
	end if;
	end function;


EP2:=function(j,i,l,k);



	d:=k-l;

	if d eq 0 then

	return EP(j,i);


	else 

	if i lt l and j lt k then 
	return i*k+j;
	elif i + d ge j then
	return (i)*(i+d)+j;
	else return (j-d)*j+2*j-i-d;
	end if;
	end if;
	end function;


EP2i:=function(n,l,k)
	if l-k eq 0 then
	return EPi(n);
	else 
	C:=exists(t){[i,j]: i,j in [0..n+l+k]| EP2(j,i,l,k) eq n};
	return t;
	end if;
	end function;



TT:=function(M);
	E:=BaseRing(M);
	O:=Eltseq(M);
	OI:=[Eltseq(x): x in O];

	lift:=function(L)
	return [Integers()!l : l in L];
	end function;

	TOE:=[lift(x): x in OI];

	return TOE;
	end function;


Inte:=function(x);
	a:=x[1][1];
	b:=x[1][2];
	c:=x[2][1];
	d:=x[2][2];

	if Valuation(c) ge 0 and Valuation(a) ge 0 and Valuation(b) ge 0 and Valuation(d) ge 0 and Valuation(a*d-b*c) eq 0 then
	return true;
	else
	return false;
	end if;
	end function;


Integ:=function(x,i);
	a:=x[1][1];
	b:=x[1][2];
	c:=x[2][1];
	d:=x[2][2];

	if Valuation(c) ge i and Valuation(a) ge 0 and Valuation(b) ge 0 and Valuation(d) eq 0 and (a*d-b*c) ne 0  then
	return true;
	else
	return false;
	end if;
	end function;

fac:=function(T1,T2,T3,u,R)


	D:=[[*r,T3(l^-1),l*] : r in R, l in NN2 | Integ(r[2]^-1*T1(l^-1)*u) and Integ(r[3]^-1*T2(l^-1))];
	return D;
	end function;



	fact:=function(D,T3)


	B:=BaseRing(T3(N2[2]));

	ch:=function(x);
	E:=Eltseq(x);
	EE:=[B! e : e in E];
	return Matrix(B,2,2,EE);
	end function;

	E:=[r : r in D | Integ(ch(r[1][1]^-1)*r[2])];

	return E;
	end function;

quatfactor:=function(Neo,T,u,s)

	l:=#T;



	D:=[[* r,n *]: r in NN2, n in Neo | &and[Integ((n[i])^-1*T[i](AO! r^-1)*u[i],s[i]): i in [1..l]] ];



	return D;



	end function;


quatfactor2:=function(Neo,T,u)

	l:=#T;




	D:=exists(t){[* r,n *]: r in NN2, n in Neo | &and[Integ((n[i])^-1*T[i](r^-1)*u[i]): i in [1..l]] };



	return t;



	end function;



quatfactor3:=function(Neo,T,u,s,j)

	l:=#T;



	D:=exists(t){[* r,n *]: r in NN2, n in Neo | &and[Integ((n[i])^-1*(T[i](AO! r^-1))*u[i],s[i]): i in [1..l]] };




	return t;



	end function;






intquatfactor:=function(Np,T,u)

	l:=#T;


	D:=exists(r){n : n in Np | &and[Inte(T[i](AO!n)*u[i]) : i in [1..l]] }; 

	   
	return r;


	end function;



	multipl:=function(X,Y,r,j)

	return [* X[k]^(r)*Y[k]^(j): k in [1..#X] *];
	end function;


OR3:=function(N,Q,T,T2,li)
	ans:=[]; 
	bns:=[];
	i:=0; 
	while i ne #Q do
	i:=i+1;
	 if Q[i] in ans then
	 ans:=ans cat [];
	else
	 ans:=ans cat [x : x in ok(Q[i],N) | x in Q];
	 bns:=bns cat [[y: y in [x : x in ok(Q[i],N) | x in Q] | Integ(T(y)) and   Integ(T2(y))][li]];
	end if;
	end while; 
	return SequenceToSet(bns);
	end function;






Val:=function(M,a,b)
	n:=NumberOfColumns(M);
	m:=Nrows(M);
	L1:=[Valuation(x): x in Eltseq(M)];

	ans:=[];
	for x in L1 do

	if x ge a or x eq Infinity() then
	ans:=ans cat [b];
	else
	ans:=ans cat [Integers()! x];
	end if;
	end for;


	L:=Matrix(Rationals(),m,n,ans);
	return L;
	end function;

VAL:=function(M);
	return Val(M,400,99);
	end function;	





slops:=function(M)
	return ValuationsOfRoots(CharacteristicPolynomial(M));
	end function;



TTT:=function(M);
	E:=BaseRing(M);
	O:=Eltseq(M);
	OI:=[Integers()! x : x in O];

	return OI;
	end function;





Fastcharp:=function(M,k);

	K:=BaseRing(M);
	n:=Ncols(M);
	P<x>:=PolynomialRing(K);
	f:=P! CharacteristicPolynomial(M);
	U:=quo<P|f>;
	res:=Eltseq(U! x^k);

	cm:=Reverse(Eltseq(f));

	Tra:=function(L);

		ans:=[* L[2] *];

		for k in [2..n+1] do;
		v:= &+[((-1)^(k+i-1))*L[k-i]*ans[i] : i in [1..k-1]];
		ans[k]:=(((-1)^(k-1))*L[k]*k +v);
		end for;

		return ans;
		end function;


	Tr:=Tra(cm);



	return &+[res[i]*Tr[i+1] : i in [1..#res]];
	end function;

Wololo:=function(M,t);

	n:=Ncols(M);
	d:=Integers()! (n/t);





	ans:=[];
	for i in [1..t] do
	ans:=ans cat [i+r*t : r in [0..d-1]];
	end for;

	N:=PermutationMatrix(Integers(),ans);



	return (N^-1)*M*N;

	end function;

Wololol:=function(M,t);

	n:=Ncols(M);
	d:=Integers()! (n/t);





	ans:=[];
	for i in [1..t] do
	ans:=ans cat [i+r*t : r in [0..d-1]];
	end for;

	N:=PermutationMatrix(Integers(),ans);



	return (N)*M*N^-1;


	end function;

Wololo2:=function(n,t);


	d:=Integers()! (n/t);





	ans:=[];
	for i in [1..t] do
	ans:=ans cat [i+r*t : r in [0..d-1]];
	end for;

	N:=PermutationMatrix(Integers(),ans);



	ans;

	end function;



batman:=function(N,i,j,ns);
	return Submatrix(N,[ns*i+1..ns*(i+1)],[ns*j+1..ns*(j+1)]);
	end function;

robin:=function(N,i,ns);
	return ValuationsOfRoots(CharacteristicPolynomial(Submatrix(N,[ns*i+1..ns*(i+1)],[ns*i+1..ns*(i+1)])));
	end function;







	at:=function(n,i);
	return Floor((Sqrt(1+8*(Floor(n/i)))-1)/2);
	end function;




Newt2:=function(M,n);
	l:=Floor(Log(2,n));



	
	p2:=[M];

	for i in [1..l] do
		p2[i+1]:=p2[i]^2;
		end for;




	pr2:=[];
	for i in [1..n] do
		v:=Intseq(i,2);
		pr2[i]:=&*[p2[j]^v[j] : j in [1..#v]];
	end for;
		


	Trac:=[Trace(pr2[i]): i in [1..n]];

	Coefs:=[Trac[1]];

	 for i in [2..n] do
		Coefs[i]:=((-1)^(i+1)*Trac[i]+ &+[(-1)^(j+1)*Coefs[i-j]*Trac[j]: j in [1..i-1]])/i;
	end for;
	return Coefs,Trac;
	end function;
 



Inertca:=function(F,c,p,f,pres,con,pow)

	Neo,Ts,kr,_,ak,bk:=Projlift(F,c,f,pres);


	l:=#Ts;

	K:=BaseRing(Codomain(Ts[1]));
	P<x>:=PolynomialRing(K);
	un:=Roots(P! f)[1][1];


	Np1:=Norm_p_elements2(F,AO,p);


	field2:=K;

	OK:=Integers(K);
	H:=[K!0, K!1, K! un, K! (1+un)]; /*this is pq(F,) specific!*/
	quoti:=quo<OK|p^pow>;
	HH:=[K! ChangePrecision(OK! x,pres) : x in quoti];
	Up2:=[Matrix(field2,2,2,[p,0,(K!j)*p^con,1]): j in HH];




	alex:=[* Matrix(BaseRing(Codomain(Ts[j])),2,2,[1,0,0,1]): j in [1..l] *]; 

	quaa2:=function(AA,u)
	a:=AA;
	a[1]:=u;
	return a;
	end function;






	UP2:=[quaa2(alex,u): u in Up2];


	Sp:=function(x)
	return [*Ts[i](x): i in [1..l] *];
	end function;

	dd:=function(n,u,Np)
	II:=intquatfactor(Np,Ts,multipl(n,u,1,-1));
	return II;
	end function;
	 /*return dd,Neo,UP2,Np1,Ts;
		
	Ex:=[* t(xx): t in Ts *]; 
		EEx:=multipl(Ex,multipl(Neo[1],UP2[1],1,-1),1,1);
		Dx:=quatfactor3(Neo,Ts,EEx,[con],8);*/
	/*xx:=dd(Neo[1],UP2[1],Np1);*/

	ans:=[* *];
	for n in Neo do
		for u in UP2 do
		x:=dd(n,u,Np1);
		/*x:=xx;*/
		E:=[* t(x): t in Ts *]; 
		EE:=multipl(E,multipl(n,u,1,-1),1,1);
		D:=quatfactor3(Neo,Ts,EE,[con],8);
		/*EE:=EEx;
		D:=Dx;*/	
		r:=D[1];
		nn:=D[2];
		rr:=[* Ts[i](r): i in [1..l] *];
		v:=multipl(nn,rr,-1,-1);
		v2:=multipl(v,EE,1,1);
		ans:=ans cat [* [*[Index(Neo,n), Index(Neo,nn)], multipl(v2,u,1,1)*] *];
		end for;
	end for;


	return  ans, #Neo, field2,kr[1],Ts,bk,[Ts[1](x): x in NN2],Neo;
	end function;




MIT2C:=function(C,CC,kw1,kw2,n,p,fdo,fiel,p1,T,chi,press,t_1,t_2: cls);
	/* This takes the Thetas in the split case and computes the matrices of the hecke operator
	*/
	maa:=Maximum(kw1,kw2);
	mii:=Minimum(kw1,kw2);
	dif:=maa-mii;

	matt:=Maximum([Maximum(EP2i(s,kw1-1,kw2-1)) : s in [0..n]]);


	pres:=matt;


	l:=fdo^2;
	KK:=fiel;
	KK2:=ChangePrecision(KK,press);

	F2:=Domain(T);

	GG:=Parent(chi);
	Cyc:=GG`TargetRing;
	FI:=Compositum(F2,Cyc);
	Comp,kro:=Completion(FI,pq(FI,p): Precision:=press);
	CC2:=ChangePrecision(Comp,press);
	fx:=DefiningPolynomial(CC2,pAdicField(CC2));
	FU:=ChangePrecision(Codomain(T),Precision(pAdicField(CC2)));
	Ry:=PolynomialRing(FU);
	fg:=Factorization(Ry! fx)[1][1];

	Ota:=function(f);
			deedee:=Degree(f);
			if deedee eq 1 then
			return FU;
			elif IsInertial(f) then
			return ext<FU|f>;
			elif IsEisenstein(f) then
			return ext<FU|f>;
			else 
			dexter:=Degree(FU,pAdicField(FU));
			return UnramifiedExtension(FU, Integers()! deedee/dexter);
			end if;
			end function;


	C4:=Ota(fg);





	Rx:=PolynomialRing(C4);
	ff:=DefiningPolynomial(FI);

	xx:=Roots(Rx! ff)[1][1];

	kap:=function(x);
		sx:=Eltseq(x);
		fl:=[C4! sx[i]*xx^(i-1): i in [1..#sx]];
		return &+fl;
		end function;

	KK2:=C4;	

	G:=Automorphisms(KK2);
	w1:=G[1];
	w2:=G[2];


	pullb:=function(x,auto)
		if x eq 0 then
			return x;
		else
		return auto(x);
		end if;
		end function;


	char:=function(x)
		return  kap(FI! chi(x@@T));
		end function;


			


	entries:=function(N,K);

		L:=Eltseq(N);
		a1:=L[1];
		b1:=L[2];
		c1:=L[3];
		d1:=L[4];



		a:=K! pullb(a1,w1);
		a2:=K!  pullb(a1,w2);
		b:=K! pullb(b1,w1);
		b2:=K!  pullb(b1,w2);

		c:=K! pullb(c1,w1);
		c2:=K!  pullb(c1,w2);

		d:=K! pullb(d1,w1);
		d2:=K!  pullb(d1,w2);

		charac:=K!  char(d);

		return [a,b,c,d,a2,b2,c2,d2,charac];

		end function;


	teichmul:=function(d1,d2,Fi,n1,n2);

	O:=Integers(Fi);
	q:=quo<O|p^3>;
	r1:=ChangePrecision(O! q!d1,press);
	r2:=ChangePrecision(O! q!d2,press);
	return (r1^n1)*(r2^n2);
	end function;
tors:=function(x);
	v:=Valuation(x);
	

	if v gt 500 then
		return x;
	else 
	y:=2^(-v)*x;
	OK:=Integers(Parent(x));
	P<t>:=PolynomialRing(OK);
	R0:=Roots(t^6-1);
	R:=[R0[i][1]: i in [1..6]];
	q:=quo<OK|4>;
	S:=[q! r : r in R];
	rus:=[x: x in q| x^2 eq 1];
	ru:=[r : r in rus| not r in S][1];
	yy:= q! y;
		if yy in S then
			 x0:= yy;
		else 
			 x0:=q! (yy*ru);
		end if;	
	xx:=[ r : r in R | (q! r) eq x0][1];
	return (2^v)*xx;
	end if;
	end function;





	CoHMF2:=function(bb,aa,dd,cc,kk1,kk2,N,FIELD);



		min:=Minimum(kk1,kk2);



		if kk1 eq kk2 then 
			v1:=0;
			v2:=0;
		elif kk1 eq min then
			di:=kk2-kk1;
			dif:=di/2;
			v1:=Integers()! dif;
			v2:=0;
		else 
			di:=kk1-kk2;
			dif:=di/2;
			v1:=0;
			v2:=Integers()! dif;
		end if;



		K:=FIELD;
		i:=dd;
		m:=bb;
		l:=aa;
		n:=cc;

		a:=N[1];
		b:=N[2];
		c:=N[3];
		d:=N[4];
		a2:=N[5];
		b2:=N[6];
		c2:=N[7];
		d2:=N[8];

		charac:=N[9];




	 	teichmul2:=function(d1,d2,Fi,n1,n2);
		O:=Integers(Fi);
		Pk<x>:=PolynomialRing(O);
		ro:=Roots(x^6-1);
		r1:=[ro[i][1]: i in [1..6] | Valuation(d1/ro[i][1]-1) gt 0][1];
		r2:=[ro[i][1]: i in [1..6] | Valuation(d2/ro[i][1]-1) gt 0][1];
		return (r1^n1)*(r2^n2);
		end function;

		if  Valuation(b) lt  press and Valuation(c) lt press then

		ff1:=[(a^(m-r))*(b^(i-m+r))*Binomial(i,m-r)*Binomial(kk1-1-i,r)*c^r*d^(-r): r in [0..m]];
		f:=&+ff1;
		coe1:=f*d^(kk1-1-i);

		elif Valuation(b) lt press and Valuation(c) gt (press-100) then

		f:=(a^(m))*(b^(i-m))*Binomial(i,m)*Binomial(kk1-i-1,0);
		coe1:=f*d^(kk1-1-i);

		elif Valuation(c) lt press and Valuation(b) gt (press-100) then
		f:=(a^(i))*Binomial(i,i)*Binomial(kk1-1-i,m-i)*(c/d)^(m-i);
		coe1:=f*d^(kk1-1-i);	

		else 
		f:=(a^(m))*Binomial(i,m)*Binomial(m,i);
		coe1:=f*d^(kk1-1-m);		

		end if;

		if Valuation(b2) lt press and  Valuation(b2) lt press   then

		ff2:=[(a2^(l-s))*(b2^(n-l+s))*Binomial(n,l-s)*Binomial(kk2-1-n,s)*c2^s*d2^(-s): s in [0..l]];
		f2:=&+ff2;
		coe2:=f2*d2^(kk2-1-n);


		elif Valuation(b2) lt press and  Valuation(c2) gt (press-100) then

		f:=(a2^(l))*(b2^(n-l))*Binomial(n,l)*Binomial(kk2-n-1,0);
		coe2:=f*d2^(kk2-1-n);

		elif Valuation(c2) lt press and  Valuation(b2) gt (press-100) then
		f:=(a2^(n))*Binomial(n,n)*Binomial(kk2-1-n,l-n)*(c2/d2)^(l-n);
		coe2:=f*d2^(kk2-1-n);	


		else 
		f:=(a2^(n))*Binomial(n,l)*Binomial(l,n);
		coe2:=f*d2^(kk2-1-n);	


		end if;

		return charac*coe1*coe2*tors(d)^(t_1)*tors(d2)^(t_2);


		end function;



	CoHMF3:=function(bb,aa,dd,cc,kk1,kk2,N,FIELD,bound1,bound2);



		min:=Minimum(kk1,kk2);



		if kk1 eq kk2 then 
			v1:=0;
			v2:=0;
		elif kk1 eq min then
			di:=kk2-kk1;
			dif:=di/2;
			v1:=dif;
			v2:=0;
		else 
			di:=kk1-kk2;
			dif:=di/2;
			v1:=0;
			v2:=dif;
		end if;



		K:=FIELD;
		i:=dd;
		m:=bb;
		l:=aa;
		n:=cc;

		a:=N[1];
		b:=N[2];
		c:=N[3];
		d:=N[4];
		a2:=N[5];
		b2:=N[6];
		c2:=N[7];
		d2:=N[8];

		charac:=N[9];
		OK:=Integers(K);
		q:=quo<OK|p>;
		d0:=ChangePrecision(K! q! d,press);
		d02:=ChangePrecision(K! q! d2,press);

		f:=p^i*Binomial(i,m)*Binomial(m,i);
		coe1:=f*d^(kk1-1)*tors(d)^(-2*i);	

	

		
		f2:=p^n*Binomial(n,l)*Binomial(l,n);
		coe2:=f2*d2^(kk2-1)*tors(d2)^(-2*n);	


	

		return charac*coe1*coe2;


		end function;



	COEFHMFS2:=function(i,j,k,l,kk1,kk2,L,FIELD);




		if L ne [* *] then

		S:=[CoHMF2(i,j,k,l,kk1,kk2,r,FIELD): r in L];

		return &+S;

		else 

		return 0;
		end if;
		end function;

	COEFHMFS3:=function(i,j,k,l,kk1,kk2,L,FIELD,b1,b2);




		if L ne [* *] then

		S:=[CoHMF3(i,j,k,l,kk1,kk2,r,FIELD,b1,b2): r in L];

		return &+S;

		else 

		return 0;
		end if;
		end function;


	P<z>:=PolynomialRing(KK2);



	ert:=[* *];
		for i,j in [1..fdo] do
		Eij:=[x: x in C | x[1] eq [i,j]];			
		E2:=[* entries(x[2][p1],KK2)  : x in Eij *];
		ert:=ert cat [* E2 *];
		end for;	

		
	
	ert2:=[* *];
		for i,j in [1..fdo] do
		Eij:=[x: x in CC | x[1] eq [i,j]];			
		E2:=[* entries(x[2][p1],KK2)  : x in Eij *];
		ert2:=ert2 cat [*E2*];
		end for;
		

    
	aa21:=function(l,n,r)
		ans2:=[];
		for j:=0 to l do
		ii1:=fi(j)[1];
		ji1:=fi(j)[2];
		 for i:=0 to n do 
		li1:=fi(i)[1];
		ki1:=fi(i)[2];
		ans2:=ans2 cat [COEFHMFS2(ii1,ji1,li1,ki1,kw1-1,kw2-1,r,KK2)]; 
		end for; 
		end for;
		return ans2;
		end function;
		
		aa2:=function(l,n,r)
	ans2:=[];
	for j:=0 to l do
	ii1:=EP2i(j,kw1-1,kw2-1)[1];
	ji1:=EP2i(j,kw1-1,kw2-1)[2];
	 for i:=0 to n do 
	li1:=EP2i(i,kw1-1,kw2-1)[1];
	ki1:=EP2i(i,kw1-1,kw2-1)[2];
	ans2:=ans2 cat [COEFHMFS2(ii1,ji1,li1,ki1,kw1-1,kw2-1,r,KK2)]; 
	end for; 
	end for;
	return ans2;
	end function;	


	arc:=function(n,r)

		ii1:=fi(n)[1];
		ji1:=fi(n)[2];
		li1:=fi(n)[1];
		ki1:=fi(n)[2];
		return COEFHMFS2(ii1,ji1,li1,ki1,kw1-1,kw2-1,r,KK2); 

		end function;


	arctic:=function(n,m,r,b1,b2)

		ii1:=fi(n)[1];
		ji1:=fi(n)[2];
		li1:=fi(m)[1];
		ki1:=fi(m)[2];
		return COEFHMFS3(ii1,ji1,li1,ki1,kw1-1,kw2-1,r,KK2,b1,b2); 

		end function;
	arctic2:=function(n,m,r)

		ii1:=fi(n)[1];
		ji1:=fi(n)[2];
		li1:=fi(m)[1];
		ki1:=fi(m)[2];
		return COEFHMFS2(ii1,ji1,li1,ki1,kw1-1,kw2-1,r,KK2); 

		end function;


	X3:=function(n);
		ask:=[];
		for i in [1..l] do
		ask:=ask cat [arc(n,ert[i])];
		end for;
		return Matrix(KK2,fdo,fdo,ask);
		end function;

		X4:=function(n,m,b1,b2);
		ask:=[];
		for i in [1..l] do
		ask:=ask cat [arctic(n,m,ert[i],b1,b2)];
		end for;
		return Matrix(KK2,fdo,fdo,ask);
		end function;

	X5:=function(n,m);
		if l gt 1 then
		ask:=[];
		for i in [1..l] do
		ask:=ask cat [arctic2(n,m,ert[i])];
		end for;
		return Matrix(KK2,fdo,fdo,ask);
		else return arctic2(n,m,ert[1]);
		end if;
		end function;



	X2:=function(i,j,r)
		if cls then 
		return Matrix(KK2,i,j,aa2(i-1,j-1,r));
		else return  Matrix(KK2,i,j,aa21(i-1,j-1,r));
		end if;
		end function;




	ant:=[];
	for i in [1..l] do 
	ant:=ant cat [X2(n,n,ert[i])];
	end for;

	
	ant2:=[];
	for i in [1..l] do 
	ant2:=ant2 cat [X2(n,n,ert2[i])];
	end for;
	



	MQT:=BlockMatrix(fdo,fdo,ant);


	
	MQT2:=BlockMatrix(fdo,fdo,ant2);
	




	return MQT,MQT2,char,T,X3,X4,X5, teichmul, ant,X2,[ert[i]: i in [1..fdo^2]] ,KK2,CoHMF2;
	end function;	
Newt:=function(M,n);

	p:=[M];

		for i in [2..n] do
		 p[i]:=M*p[i-1];
		end for;

	Trac:=[Trace(p[i]): i in [1..n]];

	Coefs:=[Trac[1]];

		 for i in [2..n] do
			Coefs[i]:=((-1)^(i+1)*Trac[i]+ &+[(-1)^(j+1)*Coefs[i-j]*Trac[j]: j in [1..i-1]])/i;
		 end for;
	return Coefs,Trac;
	end function;


ONP:=function(M,n);
	C:=Newt(M,n);
	E:=[<0,0>] cat [<i,Valuation(C[i])>: i in [1..n]];
	NP:=NewtonPolygon(E);
	S:=[s : s in Slopes(NP)];
	V:=LowerVertices(NP);	
	
	swm := [];
	lastslope:=Infinity();
	
	for i:=1 to #V-1 do
		v1:=V[i];
		v2:=V[i+1];
		mult:=v2[1]-v1[1];
		slope:=(v1[2]-v2[2])/mult;
		if #swm gt 0 and slope eq lastslope then
			swm[#swm]:=<slope, mult+swm[#swm][2]>;
		else 
			Append(~swm,<-slope,mult>);
			lastslope:=slope;
		end if;
	end for;
    return swm;


	end function;


ONPt:=function(M,n);
	C:=Newt2(M,n);
	E:=[<0,0>] cat [<i,Valuation(C[i])>: i in [1..n]];
	NP:=NewtonPolygon(E);
	S:=[s : s in Slopes(NP)];
	V:=LowerVertices(NP);	
	
	swm := [];
	lastslope:=Infinity();
	
	for i:=1 to #V-1 do
		v1:=V[i];
		v2:=V[i+1];
		mult:=v2[1]-v1[1];
		slope:=(v1[2]-v2[2])/mult;
		if #swm gt 0 and slope eq lastslope then
			swm[#swm]:=<slope, mult+swm[#swm][2]>;
		else 
			Append(~swm,<-slope,mult>);
			lastslope:=slope;
		end if;
	end for;
    return swm;


	end function;	


Bas:=function(n,s);
	B:=Sort([[i+j,i,j]: i,j in [0..n] | (i-j-s) mod 3 eq 0]);
	return B;
	end function;

Bas2:=function(n,s);
	B:=Bas(n,s);
	B2:=[];
	b:=Floor(#B/2);
		for i in [1..b] do
			x:=[y: y in B | not y in B2][1];
			B2:=B2 cat [x,[x[1]+2,x[2]+1,x[3]+1]];
		end for;
	return B2;	
	end function;	


UpOpSp:=function(pres);
	Wa,ns,fie,KE,Ts,St:=Inertca(F,pq(F,2)^2,2,x^2+x+1,pres,2,1);
	s:=[s: s in St | s^3 eq 1 and s ne 1][1];
	assert Valuation(Ts[1](s)[1][2]) gt (pres-10);
	G:=DirichletGroup(pq(F,2)^2);
	U,j:=UnitGroup(Z);
	e:=j(U.2);
	ch:=[c : c in Elements(G)| c(-1) eq 1 and c(e) eq -1][1];
	Up:=function(k_1,k_2,N,t_1,t_2);
		m:=k_2-k_1;
		V:=Bas2(N,m);
		V2:=[V[i]: i in [1..N]];
		U2,_,char,_,_,_,X5,T:=MIT2C(Wa,Wa,k_1,k_2,2,2,ns,fie,1,KE,ch,pres,t_1,t_2: cls:=false);
		KO:=Parent(X5(0,0));
		M:=Matrix(KO,N,N,[X5(f(v[2],v[3]), f(w[2],w[3])  ): v,w in V2 ] );
		return M,T,Wa,ch,char,s;
		end function;
		return Up;
	end function;	


Cheapup:=function(pres);
	K:=Completion(F,pq(F,2): Precision:=pres);
	P<x>:=PolynomialRing(K);
	a:=Automorphisms(K)[2];
	r:=Roots(x^2+x+1)[1][1];
 	r2:=Roots(9*x^2+3*x+4)[1][1];
 		assert Valuation(r2) gt 1;
 	v:=-r/3+r2;
 	d2:=(v+a(v)-1)/2;
 	d1:=-(2*r+1)*d2;
 	return d1,d2;
 	end function;




Woot:=function(k1,k2,chh,N);
	v:=k1-k2;
	n1:=k1-2;
	n2:=k2-2;
	m1:=Integers()! ((n1-1)/2);
	m2:=Integers()! ((n2-1)/2);
	F2:=Domain(chh);
	CY:=Parent(chh)`TargetRing;
	CY2:=Compositum(F2,CY);
	K2,kr2:=Completion(F2,pq(F2,2):Precision:=900);
	K,kr:=Completion(CY2,pq(CY2,2): Precision:=900);
	P<t>:=PolynomialRing(K2);
	L1:=Roots(9*t^2+3*t+4);
	L2:=Roots(t^2+t+1);
	r1:=[L1[i][1] : i in [1..2]| Valuation(L1[i][1]) gt 0][1];
	r2:=L2[1][1];
	g:=r1-r2/3;
	g2:=r1-((r2^2)/3);
	d2:=(g+g2-1)/2;
	d1:=-(2*r2+1)*d2;
	dr1:=-r2+d1;

	dd2:=kr(CY2! F2! d2@@kr2);
	dd1:=kr(CY2! F2! d1@@kr2);
	a2:=1/(3*dd2);






	ch:=function(x);
		return kr(CY2! chh(F2! (x@@kr2)));
		end function;

	 C:=function(i,j,n,x);
	 	return &+[Binomial(n-j,r)*Binomial(j,i-r)*x^r : r in [0..i]];
	 	end function;
	Om1:=function(i1,i2); 		
			return 2^(i1+i2)*d2^(n1+n2-2*i1-2*i2)*3^(m1+m2+1-i1-i2)*(-1)^(m1+m2+n1+n2+1+i1+i2);
			end function;
	Om2:=function(i1,i2,j1,j2);
			return 2^(i1+i2)*d2^(n1+n2-i1-i2-j1-j2)*3^(1-i1-i2)*C(i1,j1,n1,-2)*C(i2,j2,n2,-2);
			end function;	
	Om:=function(i1,i2,j1,j2);
		return Om2(i1,i2,j1,j2)+Om1(i1,i2)*Binomial(i1,j1)*Binomial(i2,j2)*Binomial(j1,i1)*Binomial(j2,i2);
		end function;
	Om3:=function(i1,i2); 		
			return 2^(i1+i2)*dd2^(n1+n2-2*i1-2*i2)*3^(m1+m2+1-i1-i2)*(-1)^(m1+m2+n1+n2+i1+i2)*ch(dr1);
			end function;
	Om4:=function(i1,i2,j1,j2);
			return 2^(i1+i2)*dd2^(n1+n2)*C(i1,j1,n1,-2)*C(i2,j2,n2,-2)*a2^(i1+i2)*dd2^(-j1-j2)*(ch(d2)+ch(d2*r2^2)+ch(d2*r2));                                
			end function;	
	Om5:=function(i1,i2,j1,j2);
		return Om4(i1,i2,j1,j2)+Om3(i1,i2)*Binomial(i1,j1)*Binomial(i2,j2)*Binomial(j1,i1)*Binomial(j2,i2);
		end function;


	OMG:=function(i1,i2,j1,j2);
		   return 2^(i1+i2)*d2^(n1+n2-2*i1-2*i2)*3^(1-i1-i2)*(C(i1,j1,n1,-2)*C(i2,j2,n2,-2)-((-3)^(m1+m2))*Binomial(i1,j1)*Binomial(i2,j2)*Binomial(j1,i1)*Binomial(j2,i2)*(-1)^(i1+i2));
		   end function;
	V:=Bas2(N,v);
		V2:=[V[i]: i in [1..N]];				
		M:=Matrix(K,N,N,[Om5(v[2],v[3], w[2],w[3]): v,w in V2 ] );
	return M, OMG, [ch(dr1),ch(d2),ch(d2*r2),ch(d2*(r2^2))],d1@@kr2,d2@@kr2;
	end function;




FMC:=function(n);
	G:=DirichletGroup(pq(F,2)^n);
	U,j:=UnitGroup(Z);
	e:=j(U.2);
	ch:=[x : x in Elements(G) | x(e) eq -1 and x(-1) eq 1 and Conductor(x) eq pq(F,2)^n][1];
	return ch;
	end function;


UpMatrix:=function(precision);
	return UpOpSp(precision);
	end function;

Brantmatrices:=function(pres);
	Wa,ns,fie,KE,Ts,St:=Inertca(F,pq(F,2)^2,2,x^2+x+1,pres,2,1);
	s:=[s: s in St | s^3 eq 1 and s ne 1][1];
	assert Valuation(Ts[1](s)[1][2]) gt (pres-10);	
return [Wa[i][2][1]: i in [1..#Wa]]; 
end function;
