(* ::Package:: *)

BeginPackage["CliffordDecomposition`","Q3`"]

`CliffordDecomposition`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.00 $"][[2]], " (",
  StringSplit["$Date: 2022-10-01 17:40:13 $"][[2]], ") ",
  "Ha-Eum Kim"
 ];
(*Gottesman Form*)
{ GottesmanDecompose};

(*Quisso Form*)
{ CliffordDecompose};


Begin["`Private`"]


GottesmanDecompose::usage="GottesmanDecompose[mat,{\!\(\*SubscriptBox[\(s\), \(1\)]\),\!\(\*SubscriptBox[\(s\), \(2\)]\),...}] gives a quantum circuit for a binary symplectic matrix \!\(\*
StyleBox[\"mat\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)as a list of X,Y,Z,H,S,CNOT,CY,CZ gates."

GottesmanDecompose[gotU_,qq_:{__?QubitQ},c0_:1]:=Module[

{
circ,circtemp,
gotUtemp,qqtemp,qtemp,i
},

	circ={};

	gotUtemp=gotU;
	qqtemp=qq;
	qtemp=First@qq;

	For[i=1,i<Length @ qq,i++,

		{gotUtemp,circtemp}=subGottesmanDecompose[gotUtemp,qqtemp,qtemp,c0];

		circ//=Join[circtemp,#]&;
		qqtemp=Rest@qqtemp;
		qtemp = First @ qqtemp;

];

circ//=Join[qtemp[gotUtemp/.ruleGotMtoIdx],#]&;
QuantumCircuit @@ circ

]

subGottesmanDecompose[gotU_,qq_:{__?QubitQ},q0_?QubitQ,c0_:1]:=Module[

{
control,targets,
q1,p0,p1,
swap,aa,bb,circ,
gotV
},

	{control,targets}=conjugateXZ[gotU,qq,q0,c0];

	circ={};
	q1=First @ Keys @ control;
	p0=First @ FirstPosition[qq, q0];
	p1=First @ FirstPosition[ qq, q1];

	swap=Nothing;
	If[!SameQ[q1 , q0 ],
		{swap,control,targets}=swappedAssociation[control,targets,q0,First @ Keys @control]
	];

	gotV=gotmV[gotU,control,targets,qq,p0,p1];

	{aa,bb}=controlledCircuits[targets,q0];

	PrependTo[circ,swap];
	circ//=Join[matchingassumptionCircuit[control,q0],#]&;
	circ//=Join[aa,#]&;
	PrependTo[circ,q0[6]];
	circ//=Join[bb,#]&;

	{gotV,circ}

]


gotmV[gotU_,assoc_,assot_,qq_,p0_,p1_]:=Module[

{
	newU =matchingassumptionU[gotU,assoc,p0,p1],
	vv, ixyz,i ,j,uu, ww,bb,
	l0=2 * Length @ assot
},

vv=IdentityMatrix @ l0 ;
bb=Flatten @ Lookup[assot,qq,Nothing][[;;,1]];

ixyz={SparseArray[{0,0}],SparseArray[{1,0}],SparseArray[{1,1}],SparseArray[{0,1}]};

For[i=1,i<=l0,i++,
uu=Join[vv[[i,;;2p0-2]],#,vv[[i,2p0-1;;]]]&/@ixyz;

j=1;
While[True,
ww =Mod[(uu[[j]] . newU),2];
If[ SameQ[{0,0}, ww[[{2p0-1,2p0}]]] , (*Print[j];*)Break[] ];
j++
];

ww=Drop[ww,{2p0-1,2p0}];

If[
MemberQ[{2,3},j],
ww=Mod[bb+ww,2]
];

vv[[i]]=ww;

];

vv

]

(*as real order*)
matchingassumptionU[gotU_,asso_,p0_,p1_]:=Module[
{
pp0,pp1,newU,
op0=Inverse[ First @ Values[asso] , Modulus->2] . ThePauli[1]
},

pp0={2p0-1,2p0};
pp1={2p1-1,2p1};

newU=gotU;
newU[[;;,pp1]]=gotU[[;;,pp0]];
newU[[;;,pp0]]=Mod[gotU[[;;,pp1]] . op0,2];
newU
]


bsge=BinarySymplecticGroupElements[1];
ruleGotMtoIdx=Thread[bsge->{{6},{0},{7},{6,7},{6,7,6},{7,6}}];

ruleGotVtoIdx={{0,0}->0,{1,0}->1,{1,1}->2,{0,1}->3};


controlledCircuits[asso_,q0_]:=Module[
{aa,bb,asso0},
{bb,aa}=Transpose @ 
	KeyValueMap[#1[Replace[#2,ruleGotVtoIdx,{1}]]&,asso];
{Map[ControlledU[q0,#]&, aa],Map[ControlledU[q0,#]&, bb]}
]


swappedAssociation[assoc_,assot_,q0_,q1_]:=Module[
{assonew,assonewc},
assonew=<|assoc,assot|>;
assonew[q1]= assot[q0];
assonew[q0]=assoc[q1];
assonewc=KeyTake[assonew,q0];

(*output : {circuit, control, targets}*)
{SWAP[q0,q1],assonewc,KeySort@KeyComplement[{assonew,assonewc}]}
]

matchingassumptionCircuit[asso_,q0_]:=q0[
Mod[
	ThePauli[1] . (First@Values@asso ),
2]/.ruleGotMtoIdx
]


conjugateXZ[gotU_,qq_,q0_,c0_:1]:=Module[
(*input ;
	mat : matrix/qubit that represent clifford operator;
	qq : list of qubits;
	q : name of qubit that will be control part of decomposition form;
*)
(*MISS FORM ; 
	1. when dimension of mat and qq isn't same;
*)
(* output {control, targets};
	control : single element association. Key represents the qubit that will be swapped with q0. Value represents list of two gottesman vectors of single qubit pauli operator. The first(second) one came from conjugating pauli z(x) by mat.;
	targets : multi elements associations. Keys represent the qubits that will be target part of controlled pauli operator with q0 as controlled qubit. Values represent list of two gottesman vectors of single qubit pauli operator. The first(second) one came from conjugating pauli z(x) by mat which will be operator of targets at operator A(B).;
*)
(*
I use gottesman to find pauli operators. So determinant of A and B will be 1. This guarentee we can just transform gottesman vector as pauli operator with coefficient 1;
Determinant of V is different with Determinant of U. Det[U]=-Det[V];
*)
{
d,
uu,cc,xx,zz,xz,
asso, control, targets
},

	d = First @ Dimensions @ gotU;
	d/= 2;

	uu = UnitVector[ d, First @ FirstPosition[ qq , q0 ] ];
	cc = ConstantArray[ 0, d];
	xx = Riffle[ uu, cc ];
	zz = Riffle[ cc, uu ];
	(*acted to gotU*)
	xx = xx . gotU;
	zz = zz . gotU;
	(*find noncommuting& pauli opertator*)
	xz = { Partition[xx,2], Partition[zz,2] };
	xz = Transpose @ xz;
	xz = Association@Thread[qq->xz];
	asso=If[ noncommuteQ @ xz[q0],
			KeyTake[xz,q0],
			Take[ Select[noncommuteQ][xz], {c0} ]
			];

	{control,targets}={asso,KeySort @ KeyComplement[{xz,asso}]}
]

noncommuteQ[xz_]:=(!MemberQ[ xz, {0,0} ])&&!SameQ@@xz


CliffordDecompose::usage="CliffordDecompose[mat,{\!\(\*SubscriptBox[\(s\), \(1\)]\),\!\(\*SubscriptBox[\(s\), \(2\)]\),...}] gives a quantum circuit for the Clifford operator with matrix representation \!\(\*
StyleBox[\"mat\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)as a list of X,Y,Z,H,S,CNOT,CY,CZ gates."
CliffordDecompose::wrong="`` is not Clifford matrix.";

CliffordDecompose[mat_,ss_]:=Message[CliffordDecompose::wrong,mat]/;!CliffordQ[mat]

CliffordDecompose[mat_,ss_]:=Module[
{got=GottesmanMatrix[ mat],
qc, matqc, xyz},

qc = GottesmanDecompose[ got , ss ];
xyz = gottesmanphase[ mat, qc, ss];
Join[ qc ,QuantumCircuit @@ xyz]

]

gottesmanphase[mat_,qc_,ss_]:=Module[
{opqc=Elaborate@qc,matqc,opneed},

matqc=Matrix[opqc,ss];
opneed=Elaborate@ExpressionFor[ mat . ConjugateTranspose[matqc],ss];
opneed=GottesmanVector[opneed,ss];
Select[ Thread @ FromGottesmanVector[ Partition[opneed,2], ss ],QubitQ]
]


End[]

EndPackage[]
