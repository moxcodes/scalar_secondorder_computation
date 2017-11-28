(* ::Package:: *)

(* ::Text:: *)
(*Unfortunately, as this modifies xTensor tools in some places, this package needs to sit in the global context to work properly. My apologies if this is a massive inconvenience.*)


(* ::Text:: *)
(*In order for this package to work, you will need to previously have imported at least:*)
(*<<xAct`xTensor`*)
(*<<xAct`xCoba`*)
(*<<xAct`xPert`*)
(*<<xAct`TexAct`*)


(* ::Text:: *)
(*For this package, due to the lack of good organizing structure, There will be a $3p1functions that gives the full list of functions defined herein*)


Unprotect[ChangeCovD];Unprotect[Basis];


ChangeCovD[expr_]/;Or@@Or@@@Map[!FreeQ[expr,#]&,($31Bases),{2}]:=BasisChangeCovD[expr];
CD/:ChangeCovD[expr_,PD,CD]/;Or@@Or@@@Map[!FreeQ[expr,#]&,($31Bases),{2}]:=BasisChangeCovD[expr,PD,CD];
CD/:ChangeCovD[expr_,CD,PD]/;Or@@Or@@@Map[!FreeQ[expr,#]&,($31Bases),{2}]:=BasisChangeCovD[expr,CD,PD];


(* ::Subsection:: *)
(*xTensor Modding*)


(* ::Text:: *)
(*This needs to be re-evaluated regarding whether it is really necessary to make these changes.*)


AbstractMakeDummySet[xAct`xTensor`Private`dummies_,xAct`xTensor`Private`fm_,xAct`xTensor`Private`vbundle_]:=DummySet[xAct`xTensor`Private`vbundle,List@@Select[xAct`xTensor`Private`dummies,(VBundleOfIndex[#1]===xAct`xTensor`Private`vbundle&&AIndexQ[#1])& ],If[xAct`xTensor`Private`fm&&MetricEndowedQ[xAct`xTensor`Private`vbundle],xAct`xTensor`Private`SymmetryOfMetric[xAct`xTensor`Private`FirstMetricOfVBundle[xAct`xTensor`Private`vbundle]],0]];


BasisMakeDummySet[xAct`xTensor`Private`dummies_,xAct`xTensor`Private`fm_,xAct`xTensor`Private`vbundle_,xAct`xTensor`Private`basis_]:=  DummySet[{xAct`xTensor`Private`vbundle,xAct`xTensor`Private`basis},List@@Select[xAct`xTensor`Private`dummies,(VBundleOfIndex[#1]===xAct`xTensor`Private`vbundle&&BIndexQ[#1]&&Last@#1===xAct`xTensor`Private`basis)& ],If[xAct`xTensor`Private`fm&&MetricEndowedQ[xAct`xTensor`Private`vbundle],xAct`xTensor`Private`SymmetryOfMetric[xAct`xTensor`Private`FirstMetricOfVBundle[xAct`xTensor`Private`vbundle]],0]]


xAct`xTensor`Private`ToCanonicalOne[xAct`xTensor`Private`indices_IndexList,xAct`xTensor`Private`dummies_IndexList,xAct`xTensor`Private`syms_,xAct`xTensor`Private`options___]:=Module[{xAct`xTensor`Private`order=Length[xAct`xTensor`Private`indices],xAct`xTensor`Private`sortedindices,xAct`xTensor`Private`perm,xAct`xTensor`Private`dummysets,xAct`xTensor`Private`frees,xAct`xTensor`Private`verb,xAct`xTensor`Private`not,xAct`xTensor`Private`mms,xAct`xTensor`Private`fm,xAct`xTensor`Private`repes,xAct`xTensor`Private`newsyms},{xAct`xTensor`Private`verb,xAct`xTensor`Private`not,xAct`xTensor`Private`mms}={Verbose,Notation,UseMetricOnVBundle}/. CheckOptions[xAct`xTensor`Private`options]/. Options[ToCanonical];If[xAct`xTensor`Private`verb,Print["ToCanonicalOne:: Actual configuration: ",xAct`xTensor`Private`indices]];xAct`xTensor`Private`sortedindices=IndexSort[xAct`xTensor`Private`indices];If[xAct`xTensor`Private`verb,Print["ToCanonicalOne:: Standard configuration: ",xAct`xTensor`Private`sortedindices]];xAct`xTensor`Private`repes=If[xAct`xTensor`Private`$RepeatedSingletonsQ,Union[xAct`xTensor`Private`TakeBlocked[xAct`xTensor`Private`indices]],xAct`xTensor`Private`TakeRepeated[xAct`xTensor`Private`indices]];If[xAct`xTensor`Private`verb,Print["ToCanonicalOne:: Repeated indices: ",xAct`xTensor`Private`repes]];xAct`xTensor`Private`repes=List@@RepeatedSet/@(Flatten[xAct`xTensor`Private`IndexPosition[xAct`xTensor`Private`sortedindices,#1]]&)/@xAct`xTensor`Private`repes;If[xAct`xTensor`Private`verb,Print["ToCanonicalOne:: Repeated indices: ",xAct`xTensor`Private`repes]];xAct`xTensor`Private`perm=TranslatePerm[PermutationFromTo[List@@xAct`xTensor`Private`sortedindices,List@@xAct`xTensor`Private`indices],xAct`xTensor`Private`not];If[xAct`xTensor`Private`verb,Print["ToCanonicalOne:: Permutation to be canonicalized: ",xAct`xTensor`Private`perm]];Switch[xAct`xTensor`Private`mms,
All,xAct`xTensor`Private`fm[_]:=True, 
None,xAct`xTensor`Private`fm[_]:=False,
_List,((xAct`xTensor`Private`fm[#1]:=True)&)/@xAct`xTensor`Private`mms;xAct`xTensor`Private`fm[_]:=False];If[xAct`xTensor`Private`verb,Print["dummies: ",xAct`xTensor`Private`dummies]];
(*This is what I have changed*)
xAct`xTensor`Private`dummysets=((AbstractMakeDummySet[xAct`xTensor`Private`dummies,xAct`xTensor`Private`fm[#1],#1]&)/@$VBundles)~Join~
(Join@@(Function[{bas},((BasisMakeDummySet[xAct`xTensor`Private`dummies,xAct`xTensor`Private`fm[#1],#1,bas]&)/@$VBundles)]/@$Bases));
(*xAct`xTensor`Private`dummysets=(xAct`xTensor`Private`MakeDummySet[xAct`xTensor`Private`dummies,xAct`xTensor`Private`fm[#1],#1]&)/@$VBundles;*)If[xAct`xTensor`Private`verb,Print["ToCanonicalOne:: dummysets_tmp: ",xAct`xTensor`Private`dummysets]];
xAct`xTensor`Private`dummysets=xAct`xTensor`Private`dummysets/. DummySet[xAct`xTensor`Private`man_,xAct`xTensor`Private`dums_,xAct`xTensor`Private`metricQ_]:>DummySet[xAct`xTensor`Private`man,({xAct`xTensor`Private`IndexPosition[xAct`xTensor`Private`sortedindices,#1][[1,1]],xAct`xTensor`Private`IndexPosition[xAct`xTensor`Private`sortedindices,ChangeIndex[#1]][[1,1]]}&)/@xAct`xTensor`Private`dums,xAct`xTensor`Private`metricQ];
(*/End change*)
If[xAct`xTensor`Private`verb,Print["ToCanonicalOne:: dummysets: ",xAct`xTensor`Private`dummysets]];xAct`xTensor`Private`frees=Complement[Range[xAct`xTensor`Private`order],xAct`xTensor`Private`posits[xAct`xTensor`Private`dummysets],xAct`xTensor`Private`posits[xAct`xTensor`Private`repes]];If[xAct`xTensor`Private`verb,Print["ToCanonicalOne:: Free indices: ",xAct`xTensor`Private`frees]];xAct`xTensor`Private`newsyms=xAct`xTensor`Private`Symmetry1D[xAct`xTensor`Private`syms,Inner[Rule,xAct`xTensor`Private`slot/@Range[Length[xAct`xTensor`Private`indices]],List@@xAct`xTensor`Private`indices,List]];xAct`xTensor`Private`perm=InversePerm[xAct`xTensor`Private`perm];If[xAct`xTensor`Private`verb,Print["ToCanonicalOne:: calling: ","CanonicalPerm[",xAct`xTensor`Private`perm,",",xAct`xTensor`Private`order,",",xAct`xTensor`Private`newsyms,",",xAct`xTensor`Private`frees,",",Join[xAct`xTensor`Private`dummysets,xAct`xTensor`Private`repes],",",xAct`xTensor`Private`options,"]"]];xAct`xTensor`Private`perm=CanonicalPerm[xAct`xTensor`Private`perm,xAct`xTensor`Private`order,xAct`xTensor`Private`newsyms,xAct`xTensor`Private`frees,Join[xAct`xTensor`Private`dummysets,xAct`xTensor`Private`repes],xAct`xTensor`Private`options];If[xAct`xTensor`Private`verb,Print["ToCanonicalOne:: Canonical permutation: ",xAct`xTensor`Private`perm]];xAct`xTensor`Private`perm=If[xAct`xTensor`Private`perm===0,0,InversePerm[xAct`xTensor`Private`perm]];If[xAct`xTensor`Private`perm===0,{0,xAct`xTensor`Private`indices},{If[Head[xAct`xTensor`Private`perm]===Times,-1,1],PermuteList[xAct`xTensor`Private`sortedindices,xAct`xTensor`Private`perm]}]]


(* ::Subsection:: *)
(*General utilities - Deltas and Basis simplification*)


(* ::Subsubsection:: *)
(*Cross Delta*)


(* ::Text:: *)
(*This is a toothache. I hope dearly there is a better way I have not thought of. There is probably a way to make this more agreeable with the general xTensor framework.*)


(* ::Text:: *)
(*This is the set of utility functions used to check these non-tensor kronecker deltas, and their default definitions for a general expression.*)


IsDelta[expr_]:=False;


DeltaIndex1[expr_]:=1;
DeltaIndex2[expr_]:=1;
DeltaBasis1[expr_]:=Null;
DeltaBasis2[expr_]:=Null;


DeltaBases[expr_]:={};


BasisPrefix[Basis_]:=Null;


DeltaMetric[Delta_]:=Null;


$3p1functions={IsDelta,DeltaIndex1,DeltaIndex2,DeltaBases,DeltaBasis1,DeltaBasis2,BasisPrefix,DeltaMetric};


IsDelta::usage="IsDelta[expr_] returns true if ";


(* ::Text:: *)
(*DeltaValid - this checks that the index structure of the delta matches up with the declared basis structure. *)


DeltaValid[tens_[inds__]]/;!IsDelta[tens]:=False;


DeltaValid[tens_[inds__]]/;IsDelta[tens]:=MatchQ[{inds},{DeltaIndex1[tens]*{ind1_,DeltaBasis1[tens]},DeltaIndex2[tens]*{ind2_,DeltaBasis2[tens]}}]


DeltaValid[tens_,{inds__}]/;!IsDelta[tens]:=False;


DeltaValid[tens_,{inds__}]/;IsDelta[tens]:=MatchQ[{inds},{DeltaIndex1[tens]*{ind1_,DeltaBasis1[tens]},DeltaIndex2[tens]*{ind2_,DeltaBasis2[tens]}}]


$3p1functions=$3p1functions~Join~{DeltaValid};


(* ::Text:: *)
(*CorrectedDelta - this will take a delta with an index configuration that has been mistakenly raised or lowered and convert it to the original form that must be explicitly 1's on the diagonal, multiplied by appropriate metric tensor and basis vectors.*)


CorrectedDelta[tens_[inds__]]:=(Module[{ii,TempExpr,ruleset},
ruleset={};
Check[
If[(UpIndexQ[{inds}[[2]]]&&DeltaIndex2[tens]===-1) || (DownIndexQ[{inds}[[2]]]&&DeltaIndex2[tens]==1),
ruleset=ruleset~Join~{tenss_[indices__]/;IsDelta[tenss]:>SeparateMetric[(DeltaMetric@Head@tens),DeltaBasis2@tens][tenss[indices]]};];

If[(UpIndexQ[{inds}[[1]]]&&DeltaIndex1[tens]===-1) || (DownIndexQ[{inds}[[1]]]&&DeltaIndex1[tens]==1 ),
ruleset=ruleset~Join~{tenss_[indices__]/;IsDelta[tenss]:>SeparateMetric[(DeltaMetric@Head@tens),DeltaBasis1@tens][tenss[indices]]};];

Return[tens[inds]/.{Sequence@@ruleset}];
,Return[Null];];
];);


CorrectedDelta[tens_,{inds__}]:=(Module[{ii,TempExpr,ruleset,dummyTensor},
Check[
ruleset={};
If[!BIndexQ[{inds}[[1]]]||!BIndexQ[{inds}[[2]]],
Return[Null];];
If[!(And@@(MemberQ[DeltaBases[Head@tens],#]&/@(#[[2]]&/@(UpIndex/@{inds})))),
Return[Null];];
IsDelta[dummyTensor]^=True;
xTensorQ[dummyTensor]^=True;
SlotsOfTensor[dummyTensor]^=SlotsOfTensor[tens];
TempExpr=dummyTensor[inds];
If[!(DeltaBasis1@tens==={inds}[[1]][[2]])&&!(DeltaBasis1@tens===-{inds}[[1]][[2]]),
TempExpr=TempExpr/.{tenss_[indices__]/;IsDelta[tenss]:>SeparateBasis[DeltaBasis1@tens][tenss[indices],{inds}[[1]] ]};];

If[!(DeltaBasis2@tens==={inds}[[2]][[2]])&&!(DeltaBasis2@tens===-{inds}[[2]][[2]]),
TempExpr=TempExpr/.{tenss_[indices__]/;IsDelta[tenss]:>SeparateBasis[DeltaBasis2@tens][tenss[indices],{inds}[[2]] ]};];

If[(UpIndexQ[{inds}[[2]]]&&DeltaIndex2[tens]===-1) || (DownIndexQ[{inds}[[2]]]&&DeltaIndex2[tens]==1),
TempExpr=TempExpr/.{tenss_[indices__]/;IsDelta[tenss]:>SeparateMetric[(DeltaMetric@Head@tens),DeltaBasis2@tens][tenss[indices]]};];

If[(UpIndexQ[{inds}[[1]]]&&DeltaIndex1[tens]===-1) || (DownIndexQ[{inds}[[1]]]&&DeltaIndex1[tens]==1 ),
TempExpr=TempExpr/.{tenss_[indices__]/;IsDelta[tenss]:>SeparateMetric[(DeltaMetric@Head@tens),DeltaBasis1@tens][tenss[indices]]};];
Return[TempExpr/.dummyTensor->tens];
,Return[Null];];
];);


(* ::Text:: *)
(*DeltaCanonicalize - This will automatically re-organize the set of deltas in an expression to an accepted pattern to consistently cancel equivalent expressions. *)
(*			For the main part of the code, I only ever found use for the case where the supplementary rules were those specific to the retarded coordinates.*)


DeltaCanonicalize[DeltaName_,expr_,otherJunk__]/;Head@expr===Plus:=DeltaCanonicalize[DeltaName,#,otherJunk]&/@expr;
DeltaCanonicalize[DeltaName_,expr_,rules_,OptionsPattern[]]/;!(Head@expr===Plus):=(Module[{TempExpr=expr,ii,DeltaIndices,jj,FinalList},
(*TempExpr=ExpandAll@ToCanonical@TempExpr/.rules;*)
TempExpr=ExpandAll@TempExpr/.rules;
DeltaIndices=Intersection[Sequence@@@IndicesOf[]/@(Cases[TempExpr,DeltaName[__][__],OptionValue[ProbedDepth]])/.IndexList->List,IndicesOf[Dummy][TempExpr]/.IndexList->List];
For[jj=1,jj<=Length[DeltaIndices],jj++,
With[{index = DeltaIndices[[jj]]},
TempExpr=TempExpr/.{DeltaName[Rank__][first___, index, last___]tens_[first1___ ,-index, last1___]:>DeltaName[Rank][first, DownIndex[index],last]tens[first1, UpIndex[-index],last1]};
];
];
Return[TempExpr/.rules];
]);Options[DeltaCanonicalize]={ProbedDepth->10,IndexFilter->{__,__}};


GetNewDelta[Species_,{inds1__},{inds2__}]:=(Module[{tempIndexList,newDeltaDesignation},
		tempIndexList=Union[-1*Complement[(-1*{inds1}),Intersection[(-1*{inds1}),{inds2}]],Complement[{inds2},Intersection[(-1*{inds1}),{inds2}]]];
	newDeltaDesignation={tempIndexList[[1]][[2]],tempIndexList[[2]][[2]] };
		(*If we end up with something in the same basis, and one index up, one down, we should sub directly to metric*)
		If[tempIndexList[[1]][[2]]===-tempIndexList[[2]][[2]],
			If[UpIndexQ[tempIndexList[[2]]],
				Return[DeltaMetric[Species][Sequence@@tempIndexList]];
			,
				Return[DeltaMetric[Species][Sequence@@tempIndexList]];
			];
		];
	Return[Species[Sequence@@newDeltaDesignation][Sequence@@tempIndexList]];
	]);


SwapDelta[Species_,{inds__}]:=(Module[{tempIndexList,newDeltaDesignation},	
tempIndexList={inds};
newDeltaDesignation={tempIndexList[[2]][[2]],tempIndexList[[1]][[2]] };
	(*If we end up with something in the same basis, and one index up, one down, we should sub directly to metric*)
	If[tempIndexList[[1]][[2]]===-tempIndexList[[2]][[2]],
		If[UpIndexQ[tempIndexList[[2]]],
	Return[DeltaMetric[Species][Sequence@@tempIndexList]];
			,
			Return[DeltaMetric[Species][Sequence@@tempIndexList]];
		];
	];
Return[Species[Sequence@@newDeltaDesignation][tempIndexList[[2]],tempIndexList[[1]]]];
]);


(* ::Text:: *)
(*DefDeltaSuite - This is almost always what will be used the most in fiddling with the kronecker deltas.*)
(*                              The flag here that should cause concern is the SpeedyButFragile flag - if it is not activated, I define a couple of protective rules to*)
(*                       			protect the xTensor operations from accidentally contracting into the deltas in an invalid way. Unfortunately, this seems to*)
(*                       			increase the computational overhead with more root times rules, which might be untenable for some computations.*)


DefDeltaSuite[Species_,Basis1_,Basis2_,metric_,OptionsPattern[]]:=(Module[{ii,jj},
(* Here's a bit of tricky nonesense that I'm sure isn't best practices, but it protects contract metric from causing mayhem*)
If[!OptionValue[SpeedyButFragile],
Print["Expect Some slowdowns on times operations"];
Unprotect[Times];
Metric[Species[a__][b__] expr_]^:=Species[a][b]ContractMetric[expr];
ContractBasis[Species[a__][b__]expr_]^:=Species[a][b]ContractBasis[expr];
Protect[Times];,
Print["You probably shouldn't use the argumentless xTensor contract operations on expressions with deltas. Best of Luck"];];
DeltaMetric[Species]^=metric;
DeltaBases[Species]^=DeltaBases[Species]~Join~{Basis1,Basis2};
For[ii=0,ii<16,ii++,
With[{index1Factor=Mod[ii,2]*2-1,index2Factor=Mod[IntegerPart[ii/2],2]*2-1,
index1Basis={Basis1,Basis2}[[Mod[IntegerPart[ii/4],2]+1]],index2Basis={Basis1,Basis2}[[Mod[IntegerPart[ii/8],2]+1]]},
With[{tName=Species[index1Factor*index1Basis,index2Factor*index2Basis]},
tName=Species[index1Factor*index1Basis,index2Factor*index2Basis];

DefInfo[tName]^={"tensor",""};

DependenciesOfTensor[tName]^={};
HostsOf[tName]^={};
SlotsOfTensor[tName]^={index1Factor*VBundleOfBasis@index1Basis,index2Factor*VBundleOfBasis@index2Basis};
xTensorQ[tName]^=True;
PrintAs[tName]^="\[Delta]";
Tex[tName]^="\\delta";
$Tensors=$Tensors~Join~{tName};

If[index1Factor===index2Factor&&index1Basis===index2Basis,
SymmetryGroupOfTensor[tName]^=StrongGenSet[{1,2},GenSet[Cycles[{1,2}]]];
,
SymmetryGroupOfTensor[tName]^=StrongGenSet[{},GenSet[]];];

IsDelta[tName]^=True;
DeltaIndex1[tName]^=index1Factor;
DeltaIndex2[tName]^=index2Factor;
DeltaBasis1[tName]^=index1Basis;
DeltaBasis2[tName]^=index2Basis;

(*Species/:tName[inds1__] tens_Species[inds2__]/;(Length[Union[-1*Complement[(-1*{inds1}),Intersection[(-1*{inds1}),{inds2}]],Complement[{inds2},Intersection[(-1*{inds1}),{inds2}]]]]===0)&&DeltaValid[tens[inds2]]&&DeltaValid[Species[index1Factor*index1Basis,index2Factor*index2Basis][inds1]]:=OptionValue[Dimensionality];*)

Species/:PD[stuff__][tName[inds__]]/;DeltaValid[tName[inds]]:=0;
Species/:PDOfBasis[index1Basis][stuff__][tName[inds__]]/;DeltaValid[tName[inds]]:=0;
Species/:PDOfBasis[index2Basis][stuff__][tName[inds__]]/;DeltaValid[tName[inds]]:=0;
For[jj=1,jj<=Length[OptionValue[VanishingPDs]],jj++,
Species/:OptionValue[VanishingPDs][[jj]][stuff__][tName[inds__]]/;DeltaValid[tName[inds]]:=0;
];


Species/:tName[inds__]/;!DeltaValid[tName,{inds}]&&!(CorrectedDelta[tName,{inds}]===Null):=CorrectedDelta[tName,{inds}];

If[index1Basis===Basis2&&index2Basis===Basis1,
Species/:tName[inds__]/;DeltaValid[tName,{inds}]:=SwapDelta[Species,{inds}]];

Species/:tName[{index1Factor*ind1_,index1Factor*index1Basis},{index2Factor*ind2_,index2Factor*index2Basis}]*Species[-1*index1Factor*index1Basis,-1*index2Factor*index2Basis][{-1*index1Factor*ind1_,-1*index1Factor*index1Basis},{-1*index2Factor*ind2_,-1*index2Factor*index2Basis}]=OptionValue[Dimensionality];

Species/:tName[{index1Factor*ind1_,index1Factor*index1Basis},{index2Factor*ind2_,index2Factor*index2Basis}]*Species[-1*index2Factor*index2Basis,-1*index1Factor*index1Basis][{-1*index2Factor*ind2_,-1*index2Factor*index2Basis},{-1*index1Factor*ind1_,-1*index1Factor*index1Basis}]=OptionValue[Dimensionality];

Species/:tName[{index1Factor*ind1_,index1Factor*index1Basis},{index2Factor*ind2_,index2Factor*index2Basis}]*Species[-1*index1Factor*index1Basis,otherBasis_][{-1*index1Factor*ind1_,-1*index1Factor*index1Basis},otherind_]:=GetNewDelta[Species,{{index1Factor*ind1,index1Factor*index1Basis},{index2Factor*ind2,index2Factor*index2Basis}},{{-1*index1Factor*ind1,-1*index1Factor*index1Basis},otherind}];

Species/:tName[{index1Factor*ind1_,index1Factor*index1Basis},{index2Factor*ind2_,index2Factor*index2Basis}]*Species[-1*index2Factor*index2Basis,otherBasis_][{-1*index2Factor*ind2_,-1*index2Factor*index2Basis},otherind_]:=GetNewDelta[Species,{{index1Factor*ind1,index1Factor*index1Basis},{index2Factor*ind2,index2Factor*index2Basis}},{{-1*index2Factor*ind2,-1*index2Factor*index2Basis},otherind}];

Species/:tName[{index1Factor*ind1_,index1Factor*index1Basis},{index2Factor*ind2_,index2Factor*index2Basis}]*Species[otherBasis_,-1*index1Factor*index1Basis][otherind_,{-1*index1Factor*ind1_,-1*index1Factor*index1Basis}]:=GetNewDelta[Species,{{index1Factor*ind1,index1Factor*index1Basis},{index2Factor*ind2,index2Factor*index2Basis}},{otherind,{-1*index1Factor*ind1,-1*index1Factor*index1Basis}}];

Species/:tName[{index1Factor*ind1_,index1Factor*index1Basis},{index2Factor*ind2_,index2Factor*index2Basis}]*Species[otherBasis_,-1*index2Factor*index2Basis][otherind_,{-1*index2Factor*ind2_,-1*index2Factor*index2Basis}]:=GetNewDelta[Species,{{index1Factor*ind1,index1Factor*index1Basis},{index2Factor*ind2,index2Factor*index2Basis}},{otherind,{-1*index2Factor*ind2,-1*index2Factor*index2Basis}}];

];
];
];
];
);Options[DefDeltaSuite]={SpeedyButFragile->False,VanishingPDs->{},Dimensionality->3};


(* ::Subsubsection:: *)
(*Basis Split utilities*)


BasisReplacement[tojunk_][fromJunk_]/;MemberQ[$Bases,fromJunk[[2]]]:=fromJunk:>ReleaseHold@tojunk;


BasisReplacement[tojunk_][fromJunk_]/;MemberQ[$Bases,-fromJunk[[2]]]:=fromJunk:>(Times[-1,#]&/@(ReleaseHold@tojunk));


Split31[expr_,Arguments___]/;Head[expr]===Plus:=Split31[#,Arguments]&/@expr;


Split31[expr_,Basis4_,Basis3_,OptionsPattern[]]/;!(Head[expr]===Plus):=(Module[{IndexList,TempExpr,ii,toIndex1,toIndex2,BlackListIndices,timing,jj,SumExpr},
IndexList=Cases[IndicesOf[Basis4,Dummy][expr]/.IndexList->List,{__,Basis4}];
BlackListIndices=Join[Sequence@@(Cases[IndicesOf[#][expr]/.IndexList->List,{__,Basis4}]&/@OptionValue[Blacklist] )];
(* extract all blacklisted indices - we're not changing those*)
IndexList=Complement[IndexList,Intersection[IndexList,BlackListIndices]];
TempExpr=expr;
For[ii=1,ii<=Length[IndexList],ii++,
With[{ind1=IndicesOfVBundle[VBundleOfBasis[Basis3]][[1]][[1]],ind2=IndicesOfVBundle[VBundleOfBasis[Basis3]][[1]][[2]]},
toIndex1=Unique[ind1];
toIndex2=Unique[ind2];
timing=AbsoluteTime[];
TempExpr=(TempExpr/.{expr1_ expr2_/;MemberQ[IndicesOf[Free][expr1],IndexList[[ii]]]&&MemberQ[IndicesOf[Free][expr2],-IndexList[[ii]]]:>
		(expr1/.{BasisReplacement[{toIndex1,Basis3}][IndexList[[ii]]]})*(expr2/.{BasisReplacement[{toIndex1,Basis3}][-IndexList[[ii]]]}) +
		(expr1/.{BasisReplacement[{0,Basis4}][IndexList[[ii]]]})*(expr2/.{BasisReplacement[{0,Basis4}][-IndexList[[ii]]]})});
(*if both indices are in the same term....*)
TempExpr=(TempExpr/.{tens_/;!(Head[tens]===Times)&&MemberQ[IndicesOf[Dummy][tens],IndexList[[ii]]]&&MemberQ[IndicesOf[Dummy][tens],-IndexList[[ii]]]:>
		(tens/.{BasisReplacement[{toIndex1,Basis3}][IndexList[[ii]]]}/.{BasisReplacement[{toIndex1,Basis3}][-IndexList[[ii]]]}) +
		(tens/.{BasisReplacement[{0,Basis4}][IndexList[[ii]]]}/.{BasisReplacement[{0,Basis4}][-IndexList[[ii]]]}),
		expr1_*tens_/;!(Head[tens]===Times)&&MemberQ[IndicesOf[Dummy][tens],IndexList[[ii]]]&&MemberQ[IndicesOf[Dummy][tens],-IndexList[[ii]]]:>
		expr1*(tens/.{BasisReplacement[{toIndex1,Basis3}][IndexList[[ii]]]}/.{BasisReplacement[{toIndex1,Basis3}][-IndexList[[ii]]]}) +
		expr1*(tens/.{BasisReplacement[{0,Basis4}][IndexList[[ii]]]}/.{BasisReplacement[{0,Basis4}][-IndexList[[ii]]]})});
If[OptionValue[ExpandSelfDerivs],
TempExpr=(TempExpr/.{
expr1_[index_][expr2_]/;index===IndexList[[ii]]&&MemberQ[IndicesOf[Free][expr2],-IndexList[[ii]]]:>
(expr1[index/.{BasisReplacement[{toIndex1,Basis3}][IndexList[[ii]]]}][(expr2/.{BasisReplacement[{toIndex1,Basis3}][-IndexList[[ii]]]})]) +
(expr1[index/.{BasisReplacement[{0,Basis4}][IndexList[[ii]]]}][(expr2/.{BasisReplacement[{0,Basis4}][-IndexList[[ii]]]})]),
expr2_[index_][expr1_]/;MemberQ[IndicesOf[Free][expr1],IndexList[[ii]]]&&index===-IndexList[[ii]]:>
(expr2[index/.{BasisReplacement[{toIndex1,Basis3}][-IndexList[[ii]]]}][(expr1/.{BasisReplacement[{toIndex1,Basis3}][IndexList[[ii]]]})]) +
(expr2[index/.{BasisReplacement[{0,Basis4}][-IndexList[[ii]]]}][(expr1/.{BasisReplacement[{0,Basis4}][IndexList[[ii]]]})]) });
];
];
];
Return[ContractBasis[TempExpr,Basis4]];
];);Options[Split31]={Blacklist->{},ExpandSelfDerivs->False};


ConvertContractedBases[arguments__][expr_]/;Head@expr===Plus:=
ConvertContractedBases[arguments][#]&/@expr;


ConvertContractedBases[IndFilterList_,NewBasis_,OptionsPattern[]][expr_]/;!(Head@expr===Plus):=(Module[{IndexLists,Indices,ScreenedList,VetoList},
IndexLists=(IndicesOf[Dummy,Sequence@@#][expr]/.IndexList->List)&/@IndFilterList;
ScreenedList=(IndicesOf[]/@Cases[{expr},OptionValue[PreFilter]])/.IndexList->List;
VetoList=IndicesOf[]/@Cases[{expr},OptionValue[OmitFilter]]/.IndexList->List;
Indices=DeleteDuplicates[UpIndex/@Intersection[Join@@IndexLists,Join@@ScreenedList]];
Indices=DeleteDuplicates@Complement[Indices,Intersection[Indices,UpIndex/@(Join@@VetoList)]];
Return[(expr/.(
(Union[
With[{ind=DummyIn[VBundleOfBasis[NewBasis]]},tens_[first___,#,last___][arg_]:>tens[first,{ind,NewBasis},last][arg]Basis[{-ind,-NewBasis},#]]&/@Indices,
With[{ind=DummyIn[VBundleOfBasis[NewBasis]]},tens_[first___,-#,last___][arg_]:>tens[first,{-ind,-NewBasis},last][arg]Basis[{ind,NewBasis},-#]]&/@Indices,
With[{ind=DummyIn[VBundleOfBasis[NewBasis]]},der_[arg_][tens_[first___,#,last___]]:>der[arg][(tens[first,{ind,NewBasis},last]Basis[{-ind,-NewBasis},#])/.OptionValue[ImmediateDerivativeRule]]]&/@Indices,
With[{ind=DummyIn[VBundleOfBasis[NewBasis]]},der_[arg_][tens_[first___,-#,last___]]:>der[arg][(tens[first,{-ind,-NewBasis},last]Basis[{ind,NewBasis},-#])/.OptionValue[ImmediateDerivativeRule]]]&/@Indices,
With[{ind=DummyIn[VBundleOfBasis[NewBasis]]},tens_[first___,#,last___]:>tens[first,{ind,NewBasis},last]Basis[{-ind,-NewBasis},#]]&/@Indices,
With[{ind=DummyIn[VBundleOfBasis[NewBasis]]},tens_[first___,-#,last___]:>tens[first,{-ind,-NewBasis},last]Basis[{ind,NewBasis},-#]]&/@Indices ])))//OptionValue[SplitFunction]];
]);Options[ConvertContractedBases]={SplitFunction->Identity,PreFilter->(__),ImmediateDerivativeRule->{},OmitFilter->{Null}};


GenerateNewDummies[expr_]/;Head@expr===Plus:=GenerateNewDummies/@expr;


GenerateNewDummies[expr_]/;!(Head@expr===Plus):=(Module[{DummyList,ii,TempExpr},
DummyList=UpIndex/@(IndicesOf[Dummy][expr]/.IndexList->List);
TempExpr=expr;
For[ii=1,ii<=Length[DummyList],ii++,
If[BIndexQ[DummyList[[ii]]],
With[{ind={Unique[DummyList[[ii]][[1]]],DummyList[[ii]][[2]]}},
TempExpr=TempExpr//.{DummyList[[ii]]:>ind,-DummyList[[ii]]:>-ind}];,
With[{ind=Unique[DummyList[[ii]]]},
TempExpr=TempExpr//.{DummyList[[ii]]:>ind,-DummyList[[ii]]:>-ind};
];
];
];Return[TempExpr];
]);


GeneratePatternDummies[expr_]/;Head@expr===Plus:=GeneratePatternDummies/@expr;


GeneratePatternDummies[expr_]/;!(Head@expr===Plus):=(Module[{DummyList,ii,TempExpr},
DummyList=UpIndex/@(IndicesOf[Dummy][expr]/.IndexList->List);
TempExpr=expr;
For[ii=1,ii<=Length[DummyList],ii++,
If[BIndexQ[DummyList[[ii]]],
With[{ind={ToExpression[ToString[Unique[DummyList[[ii]][[1]]]]<>"_"],DummyList[[ii]][[2]]}},
TempExpr=TempExpr//.{DummyList[[ii]]:>ind,-DummyList[[ii]]:>-ind}];,
With[{ind=Unique[DummyList[[ii]]]},
TempExpr=TempExpr//.{DummyList[[ii]]:>ind,-DummyList[[ii]]:>-ind};
];
];
];Return[TempExpr];
]);


VBundleIndex[Index_?AbstractIndexQ]:=Index;


VBundleIndex[Index_?BIndexQ]:=Index[[1]];


SortDummies[expr_]/;(Head[expr]===Plus):=SortDummies/@expr;


SortDummies[expr_]/;!(Head[expr]===Plus):=(Module[{IndicesList,ii,UsedVBundleIndices,IndexReplacementRules,FreeIndices},
(*Presume that all of the other utilities have put everything in a good order*)
If[!(Head[List@@expr]===List),Return[expr];];
IndicesList=DeleteDuplicates[UpIndex/@(Join@@IndicesOf[]/@(List@@(expr))/.IndexList->List)];
FreeIndices=DeleteDuplicates[UpIndex/@(IndicesOf[Free][expr]/.IndexList->List)];
(*Presume that xTensor has printed this expression before, and that therefore there are enough indices constructed in the VBundles*)
IndicesList=(DeleteCases[IndicesList,Alternatives@@FreeIndices|LI[n_]]);
UsedVBundleIndices=VBundleIndex/@FreeIndices;
IndexReplacementRules={};
For[ii=1,ii<=Length[IndicesList],ii++,
With[{NextVBundleIndex=First@Complement[Join@@IndicesOfVBundle[VBundleOfIndex[IndicesList[[ii]]]]
,UsedVBundleIndices]},
If[BIndexQ[IndicesList[[ii]]],
IndexReplacementRules=IndexReplacementRules~Join~{IndicesList[[ii]]->{NextVBundleIndex,IndicesList[[ii]][[2]]},
-IndicesList[[ii]]->{-NextVBundleIndex,-IndicesList[[ii]][[2]]}}
];
If[AbstractIndexQ[IndicesList[[ii]]],
IndexReplacementRules=IndexReplacementRules~Join~{IndicesList[[ii]]->NextVBundleIndex,-IndicesList[[ii]]->-NextVBundleIndex}
];
UsedVBundleIndices=UsedVBundleIndices~Join~{NextVBundleIndex};
];
];Return[expr/.IndexReplacementRules];
])


(* ::Subsection:: *)
(*Global definitions*)


(* ::Subsubsection:: *)
(*3+1 Basis definition calls*)


$31Bases={};


Def31Basis[basis_,tanspace4_,tanspace3_,OptionsPattern[]]:=Module[{},
DefBasis[basis,tanspace4,{0,1,2,3},BasisColor->OptionValue[BasisColor],FormatBasis->OptionValue[FormatBasis],
							ProtectNewSymbol->OptionValue[ProtectNewSymbol],Dagger->OptionValue[Dagger],
							ExtendedFrom->OptionValue[ExtendedFrom],MetricInBasis->OptionValue[MetricInBasis],
							epsilonOrientationOfMetric->OptionValue[epsilonOrientationOfMetric],
							DependenciesOfBasis->OptionValue[DependenciesOfBasis],
							DefInfo->OptionValue[DefInfo],Master->OptionValue[Master]];
DefBasis[ToExpression[ToString[basis]<>"3"],tanspace3,{1,2,3},
							BasisColor->OptionValue[BasisColor],FormatBasis->OptionValue[FormatBasis],
							ProtectNewSymbol->OptionValue[ProtectNewSymbol],Dagger->OptionValue[Dagger],
							ExtendedFrom->OptionValue[ExtendedFrom],MetricInBasis->OptionValue[MetricInBasis],
							epsilonOrientationOfMetric->OptionValue[epsilonOrientationOfMetric],
							DependenciesOfBasis->OptionValue[DependenciesOfBasis],
							DefInfo->OptionValue[DefInfo],Master->OptionValue[Master]];
If[OptionValue[PreferredSplit]==None,
$31Bases=$31Bases~Join~{{basis,ToExpression[ToString[basis]<>"3"],
						Split31[#,basis,ToExpression[ToString[basis]<>"3"]]&}}
,$31Bases=$31Bases~Join~{{basis,ToExpression[ToString[basis]<>"3"],OptionValue[PreferredSplit]}}
];
Dagger[BasisChristoffel[basis]]^=BasisChristoffel[basis];
DefInfo[BasisChristoffel[basis]]^=False;
DependenciesOfTensor[BasisChristoffel[basis]]^={MasterOf[VBundleOfBasis[basis]]};

HostsOf[BasisChristoffel[basis]]^={MasterOf[VBundleOfBasis[basis]],VBundleOfBasis[basis]};
PrintAs[BasisChristoffel[basis]]^="\[CapitalGamma]["<>ToString[basis]<>"]";
SlotsOfTensor[BasisChristoffel[basis]]^={VBundleOfBasis[basis],-VBundleOfBasis[basis],-VBundleOfBasis[basis]};
xTensorQ[BasisChristoffel[basis]]^=True;
$Tensors=$Tensors~Join~{BasisChristoffel[basis]};
SymmetryGroupOfTensor[BasisChristoffel[basis]]^=StrongGenSet[{2,3},GenSet[Cycles[{2,3}]]];
];
Options[Def31Basis]={PreferredSplit->None,
 BasisColor->RGBColor[1,0,0],FormatBasis->Automatic,ProtectNewSymbol:>$ProtectNewSymbols,
 Dagger->Real,ExtendedFrom->Null,MetricInBasis->{},epsilonOrientationOfMetric->{Null,1},
 DependenciesOfBasis->{},DefInfo->{"basis",""},Master->Null};


SetPreferredSplit::BasisError = "Basis supplied not yet declared as a 3+1 basis"


SetPreferredSplit[bas_,SplitFunction_]:=Module[{ii=1},
While[!($31Bases[[ii]][[1]]===bas) && ii<=Length[$31Bases],ii++];
If[i>Length[$31Bases],Message[SetPreferredSplit::BasisError]];
$31Bases=ReplacePart[$31Bases,ii->ReplacePart[$31Bases[[ii]],3->SplitFunction]];
];


GetPreferredSplit::BasisError = "Basis supplied not yet declared as a 3+1 basis"


GetPreferredSplit[bas_]:=Module[{ii=1},
While[ii<=Length[$31Bases]&&!($31Bases[[ii]][[1]]===bas) ,ii++];
If[i>Length[$31Bases],Message[SetPreferredSplit::BasisError]];
Return[$31Bases[[ii]][[3]]];
];


PDTemp/:PDTemp[{a_,bas1_}][Basis[{b_,bas2_},{c_,bas3_}]]:=PDBasis[{a,bas1},{b,bas2},{c,bas3}];


SeparateBasisForce[bas_][expr_Plus]:=SeparateBasisForce[bas][#]&/@expr;
SeparateBasisForce[bas_][expr_Times]:=SeparateBasisForce[bas][#]&/@expr;


NoSeparate={PDBasis,Basis};


SeparateBasisForce[bas_][expr_]:=Module[{CDTempForm=(expr//.toCDTemp)/.{PD->PDTemp},indSample},
indSample[]:=Unique[IndicesOfVBundle[VBundleOfBasis[bas]][[1]][[1]]];
Return[
(CDTempForm//.{CDTemp[pre___,{a_,B_},post___][tens_[inds___]]/;!MemberQ[{bas,-bas,Form3[bas],-Form3[bas]},B]
								:>Module[{indval=indSample[],sg=-BoolToSign[UpIndexQ[{a,B}]]},
									Basis[{a,B},{sg*indval,sg*bas}]*CDTemp[pre,{-sg*indval,-sg*bas},post][tens[inds]]],
			  CDTemp[inds___][tens_[pre___,{a_,B_},post___]]/;!MemberQ[{bas,-bas,Form3[bas],-Form3[bas]},B]
								:>Module[{indval=indSample[],sg=-BoolToSign[UpIndexQ[{a,B}]]},
								    Basis[{a,B},{sg*indval,sg*bas}]*CDTemp[inds][tens[pre,{-sg*indval,-sg*bas},post]]],
			  PDTemp[{a_,B_}][exp_]/;!MemberQ[{bas,-bas,Form3[bas],-Form3[bas]},B]
								:>Module[{indval=indSample[],sg=-BoolToSign[UpIndexQ[{a,B}]]},
									Basis[{a,B},{sg*indval,sg*bas}]*PDTemp[{-sg*indval,-sg*bas}][exp]],
			  tens_[pre___,{a_,B_},post___]/;!MemberQ[{bas,-bas,Form3[bas],-Form3[bas]},B]
								&&!MemberQ[NoSeparate,tens]
								:>Module[{indval=indSample[],sg=-BoolToSign[UpIndexQ[{a,B}]]},
								Basis[{a,B},{sg*indval,sg*bas}]*tens[pre,{-sg*indval,-sg*bas},post]]}
			//.fromCDTemp//Expand)/.PDTemp->PD
];];


(*SeparateBasisForce[bas_][tens_[A__]]:=Module[{inds=Unique[IndicesOfVBundle[VBundleOfBasis[bas]][[1]][[1]]]&/@Range[Length[{A}]]},
Return[Times@@(Basis[{A}[[#]],{BoolToSign[DownIndexQ[{A}[[#]]]]*inds[[#]],BoolToSign[DownIndexQ[{A}[[#]]]]*bas}]&/@Range[Length[{A}]])
				*tens@@({-(BoolToSign[DownIndexQ[{A}[[#]]]])*inds[[#]],-(BoolToSign[DownIndexQ[{A}[[#]]]])*bas}&/@Range[Length[{A}]])];];*)


BasisConvertTrace[frombas_][A__][tens_]:=tens[A]//SeparateBasisForce[frombas]//(GetPreferredSplit[frombas]);
(* TensorExp=(tens@@({-#,-Ret}&/@DummyList))//SeparateBasis[frombas]//(GetPreferredSplit[frombas]);
 FullExp=Inner[Basis[{#1,-Ret},{#2,Ret}]&,List[A],DummyList,Times]*TensorExp;
 Return[ContractBasis[FullExp,tobas]];*)


BasisConvertTrace[frombas_][tens_[A__]]:=
BasisConvertTrace[frombas][A][tens];


(* ::Subsubsection:: *)
(*Canon Utility functions*)


BoolToSign[True]:=1;
BoolToSign[False]:=-1;


(* ::Subsubsection:: *)
(*Covariant derivative fixes*)


Unprotect[ChangeCovD];Unprotect[CD];


(* ::Text:: *)
(*First, intercept the evaluation of this if there are any of our basis indices present*)


(* ::Text:: *)
(*TODO: make this intercept and redirect to appropriate function for the basis present.*)


ChangeCovD[expr_]/;Or@@Or@@@Map[!FreeQ[expr,#]&,($31Bases),{2}]:=BasisChangeCovD[expr];
CD/:ChangeCovD[expr_,PD,CD]/;Or@@Or@@@Map[!FreeQ[expr,#]&,($31Bases),{2}]:=BasisChangeCovD[expr,PD,CD];
CD/:ChangeCovD[expr_,CD,PD]/;Or@@Or@@@Map[!FreeQ[expr,#]&,($31Bases),{2}]:=BasisChangeCovD[expr,CD,PD];


BasisChangeCovD[expr_Plus]:=BasisChangeCovD/@expr;
BasisChangeCovD[expr_Times]:=BasisChangeCovD/@expr;
BasisChangeCovD[expr_Plus,d1_,d2_]:=BasisChangeCovD[#,d1,d2]&/@expr;
BasisChangeCovD[expr_Times,d1_,d2_]:=BasisChangeCovD[#,d1,d2]&/@expr;


BasisChangeCovD[expr_]/;FreeQ[expr,CD]:=expr;
BasisChangeCovD[expr_,d1_,d2_]/;FreeQ[expr,d1]:=expr;


toCDTemp={CDTemp[a__][CD[b_][expr_]]:>CDTemp[a,b][expr],
				CD[a_][expr_]:>CDTemp[a][expr]};


fromCDTemp={CDTemp[A___][expr_]/;Length[{A}]>=1:>CDTemp[Sequence@@Delete[{A},Length[{A}]]][CD[{A}[[Length[{A}]]]][expr]],
			CDTemp[][expr_]:>expr};


toPDTemp={PDTemp[a__][PD[b_][expr_]]:>PDTemp[a,b][expr],
				PD[a_][expr_]:>PDTemp[a][expr]};


fromPDTemp={PDTemp[A___][expr_]/;Length[{A}]>=1:>PDTemp[Sequence@@Delete[{A},Length[{A}]]][PD[{A}[[Length[{A}]]]][expr]]};


PDTemp[][expr_]:=expr;


PDTemp[A__][expr_Plus]:=PDTemp[A]/@expr;
PDTemp[A__][expr_Times]:=Plus@@((PDTemp[A][expr[[#]]]*Times@@Delete[List@@expr,#])&/@Range[Length[expr]]);


CDTemp[A__][expr_Plus]:=CDTemp[A]/@expr;
CDTemp[A__][expr_Times]:=Plus@@((CDTemp[A][expr[[#]]]*Times@@Delete[List@@expr,#])&/@Range[Length[expr]]);


BasisChangeCovD[expr_,d1_,d2_]/;MatchQ[expr/.toCDTemp,CDTemp[___][tens_[inds___]]]&&d1===CD&&d2===PD:=BasisChangeCovD[expr];


(* ::Text:: *)
(*These functions could be written in a more general way. Though, more general ways have edge cases where they aren't valid. This is a pretty reasonable first pass that is assured correct.*)


(* ::Text:: *)
(*TODO: this fails for larger than 2 derivs due to christoffel stuff. The choice of the basis is not guarunteed for more than 2*)


BasisChangeCovD[expr_]/;MatchQ[expr/.toCDTemp,CDTemp[___][tens_[inds___]]]:=Module[{CDTempForm=expr//.toCDTemp,CDInds,fullinds,abstInds,forwardMap,backwardMap,ii=1},
	fullinds=(CDTempForm/.{CDTemp[A___][_]:>{A}})~Join~(CDTempForm/.{CDTemp[___][tens_[LI[o_]inds___]]:>{inds},CDTemp[___][tens_[inds___]]:>{inds}});
	abstInds=UniqueIndex[Form4[#[[2]]]] &/@fullinds;
	forwardMap=(fullinds[[#]]/;(ii==#)&&(IntegerQ[ii++])->abstInds[[#]])&/@Range[Length[fullinds]];
	backwardMap=(abstInds[[#]]->fullinds[[#]])&/@Range[Length[fullinds]];
	Return[(ChangeCovD[expr/.forwardMap]//ExpandAll)/.{ChristoffelCD[inds__]:>BasisChristoffel[Form4[AbsBasis[(Intersection[{inds},abstInds][[1]]/.backwardMap)[[2]]]]][inds]}
		/.backwardMap];
];


BasisChangeCovD[expr_,d1_,d2_]/;MatchQ[expr/.toPDTemp,PDTemp[___][tens_[inds___]]]&&d1===PD&&d2===CD:=Module[{PDTempForm=expr//.toPDTemp,fullinds,abstInds,forwardMap,backwardMap,ii=1},
	fullinds=(PDTempForm/.{PDTemp[A___][_]:>{A}})~Join~(PDTempForm/.{PDTemp[___][tens_[LI[o_],inds___]]:>{inds}}/.{PDTemp[___][tens_[inds___]]:>{inds}});
	abstInds=UniqueIndex[Form4[#[[2]]]] &/@fullinds;
	forwardMap=(fullinds[[#]]/;(ii==#)&&(IntegerQ[ii++])->abstInds[[#]])&/@Range[Length[fullinds]];
	backwardMap=(abstInds[[#]]->fullinds[[#]])&/@Range[Length[fullinds]];
	Return[ChangeCovD[expr/.forwardMap,PD,CD]/.{ChristoffelCD[inds__]:>BasisChristoffel[Form4[AbsBasis[(Intersection[{inds},abstInds][[1]]/.backwardMap)[[2]]]]][inds]}
		/.backwardMap];
];


(* ::Subsubsection:: *)
(*Automation functions*)


ClearAll[CheckpointGenerate3p1]


CheckpointGenerate3p1[tens_[LI[n_],A__],OptionsPattern[]][rulename_][filename_][simplifyFunc_]:=Module[{ii,bas,temprule,
	indexList={},rangeVal=2,tensFunc},
If[OptionValue[UpAndDownInds],
 indexList=({{0,{A}[[#1]][[2]]},{0,-{A}[[#1]][[2]]},
   {UniqueIndex[Form3[{A}[[#1]][[2]]]],Form3[{A}[[#1]][[2]]]},
   {-UniqueIndex[Form3[{A}[[#1]][[2]]]],-Form3[{A}[[#1]][[2]]]}}&)/@Range[Length[{A}]];
  rangeVal=4;
,
indexList=({{0,{A}[[#1]][[2]]},{UniqueIndex[Form3[{A}[[#1]][[2]]]],Form3[{A}[[#1]][[2]]]}}&)/@Range[Length[{A}]];
];
If[!FileExistsQ[filename],
   tensFunc[indNums__]:=(tens[LI[n],Sequence@@((indexList[[#]][[{indNums}[[#]]]]//GenericIndex)&)/@Range[Length[{indNums}]]]
  							->simplifyFunc[tens[Sequence@@((indexList[[#1]][[{indNums}[[#1]]]]&)/@Range[Length[{indNums}]])]]);
   rulename=Flatten[Outer[tensFunc,Sequence@@(Range[rangeVal]&)/@Range[Length[{A}]]]];
DumpSave[filename,rulename];
,
DumpGet[filename];
];
];Options[CheckpointGenerate3p1]={UpAndDownInds->False};


CheckpointGenerate3p1[tens_[A__],OptionsPattern[]][rulename_][filename_][simplifyFunc_]:=Module[{ii,bas,temprule,
	indexList={},rangeVal=2,tensFunc},
If[OptionValue[UpAndDownInds],
 indexList=({{0,{A}[[#1]][[2]]},{0,-{A}[[#1]][[2]]},
   {UniqueIndex[Form3[{A}[[#1]][[2]]]],Form3[{A}[[#1]][[2]]]},
   {-UniqueIndex[Form3[{A}[[#1]][[2]]]],-Form3[{A}[[#1]][[2]]]}}&)/@Range[Length[{A}]];
  rangeVal=4;
,
indexList=({{0,{A}[[#1]][[2]]},{UniqueIndex[Form3[{A}[[#1]][[2]]]],Form3[{A}[[#1]][[2]]]}}&)/@Range[Length[{A}]];
];
If[!FileExistsQ[filename],
   tensFunc[indNums__]:=(tens[Sequence@@((indexList[[#]][[{indNums}[[#]]]]//GenericIndex)&)/@Range[Length[{indNums}]]]
  							->simplifyFunc[tens[Sequence@@((indexList[[#1]][[{indNums}[[#1]]]]&)/@Range[Length[{indNums}]])]]);
   rulename=Flatten[Outer[tensFunc,Sequence@@(Range[rangeVal]&)/@Range[Length[{A}]]]];
DumpSave[filename,rulename];
,
DumpGet[filename];
];
];Options[CheckpointGenerate3p1]={UpAndDownInds->False};


Generate3p1[tens_[A__],OptionsPattern[]][rulename_][simplifyFunc_]:=Module[{ii,bas,temprule,
	indexList={},rangeVal=2,tensFunc},
If[OptionValue[UpAndDownInds],
 indexList=({{0,{A}[[#1]][[2]]},{0,-{A}[[#1]][[2]]},
   {UniqueIndex[Form3[{A}[[#1]][[2]]]],Form3[{A}[[#1]][[2]]]},
   {-UniqueIndex[Form3[{A}[[#1]][[2]]]],-Form3[{A}[[#1]][[2]]]}}&)/@Range[Length[{A}]];
  rangeVal=4;
,
indexList=({{0,{A}[[#1]][[2]]},{UniqueIndex[Form3[{A}[[#1]][[2]]]],Form3[{A}[[#1]][[2]]]}}&)/@Range[Length[{A}]];
];
   tensFunc[indNums__]:=(tens[Sequence@@((indexList[[#]][[{indNums}[[#]]]]//GenericIndex)&)/@Range[Length[{indNums}]]]
  							->simplifyFunc[tens[Sequence@@((indexList[[#1]][[{indNums}[[#1]]]]&)/@Range[Length[{indNums}]])]]);
   rulename=Flatten[Outer[tensFunc,Sequence@@(Range[rangeVal]&)/@Range[Length[{A}]]]];
];Options[Generate3p1]={UpAndDownInds->False};


ConvertToBasis[TensPatt_][bas_][expr_]:=Module[{basCombo=(bas|Form3[bas]|-bas|-Form3[bas])},
Return[expr//.
{Tens_[first___,ind_,last___]/;FreeQ[Tens[first,ind,last],LI]&&MatchQ[Tens,TensPatt]&&!MatchQ[ind,{_,basCombo}]:>Module[{a},Basis[ind,-{a,bas}]Tens[first,{a,bas},last]]
,Tens_[LI[o_],first___,ind_,last___]/;FreeQ[{ind},LI]&&MatchQ[Tens,TensPatt]&&!MatchQ[ind,{_,basCombo}]:>Module[{a},Basis[ind,-{a,bas}]Tens[LI[o],first,{a,bas},last]]}];];


(* ::Subsubsection:: *)
(*Miscellaneous functions*)


BasisColorsOff[]:=((InactiveBasisColor[#]^=BasisColor[#])&/@$Bases;(BasisColor[#]^=RGBColor[0,0,0])&/@$Bases;)


BasisColorsOn[]:=((BasisColor[#]^=InactiveBasisColor[#])&/@$Bases;)


ClearMemory := Module[{},
             Unprotect[In, Out];
             Clear[In, Out];
             Protect[In, Out];
             ClearSystemCache[];
             ];


Form3[basis_?BasisQ]:=ToExpression[ToString[basis]<>"3"];
Form3[-basis_?BasisQ]:=-ToExpression[ToString[basis]<>"3"];


Form4[basis_?BasisQ]:=Module[{ii=1},
While[ii<=Length[$31Bases],
	If[basis===$31Bases[[ii]][[1]] || basis===$31Bases[[ii]][[2]],
		Return[$31Bases[[ii]][[1]]];];
	ii++;
];];
Form4[-basis_?BasisQ]:=Module[{ii=1},
While[ii<=Length[$31Bases],
	If[basis===$31Bases[[ii]][[1]] || basis===$31Bases[[ii]][[2]],
		Return[-$31Bases[[ii]][[1]]];];
	ii++;
];];
AbsBasis[basis_?BasisQ]:=basis;AbsBasis[-basis_?BasisQ]:=basis;


UniqueIndex[basis_?BasisQ]:=Unique[IndicesOfVBundle[VBundleOfBasis[basis]][[1]][[1]]];
UniqueIndex[-basis_?BasisQ]:=-Unique[IndicesOfVBundle[VBundleOfBasis[basis]][[1]][[1]]];


GenericIndex[{ind_,bas_}]:={ToExpression[ToString[ind]<>"_"],bas};
