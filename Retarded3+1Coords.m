(* ::Package:: *)

(* ::Text:: *)
(*The dependency tree in Mathematica is problematic with respect to xTensor - redundant definitions cause errors throughout. So, this package will include no imports to xTensor or the other utilities that I've made. To work, you will need the following import calls before importing this package:*)
(*<<xAct`xTensor`*)
(*<<xAct`xCoba`*)
(*<<xAct`xPert`*)
(*<<xAct`TexAct`*)
(*<<"<working directory>/3+1Utils.m"*)


(* ::Subsection:: *)
(*Retarded Manifold initiation*)


(* ::Subsubsection:: *)
(*xTensor definitions*)


DefManifold[M4,4,IndexRange[a,f]];


DefMetric[-1,met[-a,-b],CD,PrintAs->"g"];
DefMetricPerturbation[met,metpert,\[Epsilon]];


PrintAs[metpert]^="g";


(* ::Text:: *)
(*In the course of the computation, I'd like a way of compactly expanding a 3+1 split without either making a full coordinate decomposition or having*)
(*very long expressions through various normal and projection contractions. So, we define the a 3-dimensional index set:*)


DefVBundle[TangentM3,M4,3,IndexRange[i,n]];
MetricsOfVBundle[TangentM3]^={met};


(* ::Text:: *)
(*This removes an xTensor rule that identifies the zeroth-order perturbed metric with the original metric symbol - in the body of my computation, this ambiguity would cause frustrations.*)


metpert[xAct`xTensor`LI[0], Pattern[xAct`xPert`Private`indices$, BlankNullSequence[]]]=.;


(* ::Text:: *)
(*We have a tangent space for the primed submanifold and for the unprimed manifold (note that these overlap on the worldline)*)


(* ::Text:: *)
(*In order to make tensor declarations less of a pain, we'll create a function that generates the tensors with all appropriate indices. *)


(* ::Text:: *)
(*For each space and subspace, we have a basis for the retarded coordinates, and a basis for the frame components: (these will get to be purple and cyan, respectively)*)


(* ::Text:: *)
(*Ret - Retarded coordinates, take values 0-4, have coordinate singularity at r->0*)
(*Ret3 - Hypersurface-only versions of the retarded coordinates*)
(*Fra - Orthonormal frame coordinates. Final values are preferred in these, as they remain well-defined at the worldline*)
(*Fra3 - 1-3 versions of the Orthonormal frame coordinates - these point explicitly in spatial directions.*)
(*See [Poisson LRR] for more details for the distinction between Retarded Coordinate and Frame indices*)


Def31Basis[Ret,TangentM4,TangentM3,BasisColor->RGBColor[.7,0,.7]];
Def31Basis[Fra,TangentM4,TangentM3,BasisColor->RGBColor[0,.7,.7]];


(* ::Text:: *)
(*Texing the colored indices would be problematic, so manually define some rules to make that process easier*)


xAct`TexAct`Private`TexUpIndex[{any_,Fra}]:="\\hat{"<>ToString[any]<>"}";
xAct`TexAct`Private`TexUpIndex[{any_,Fra3}]:="\\hat{"<>ToString[any]<>"}";
xAct`TexAct`Private`TexUpIndex[{any_,Ret}]:=ToString[any];
xAct`TexAct`Private`TexUpIndex[{any_,Ret3}]:=ToString[any];


(* ::Text:: *)
(*The second of these may be a bit close to what primed indices may eventually be, but I haven't yet actually had need of the primed basis components, so they might not be necessary.*)


For[ii=1,ii<=111,ii++,
xAct`TexAct`Private`TexUpIndex[{ToExpression["n"<>ToString[ii]],Ret3}]="n_{"<>ToString[ii]<>"}";
xAct`TexAct`Private`TexUpIndex[{ToExpression["n"<>ToString[ii]],Fra3}]="\\hat{n}_{"<>ToString[ii]<>"}";]


Ret::usage="Ret is the xTensor basis for the abstract indices (unhatted greek in [Poisson LRR])";
Fra::usage="Fra is the xTensor basis for the frame indices (hatted in [Poisson LRR]). Any tensor with only frame indices should be considered a scalar";
Fra3::usage="Fra3 is the xTensor basis for the frame indices orthoganal to the worldline";
Ret3::usage="Ret3 is the xTensor basis for the abstract indices restricted to the future light cone";


(* ::Subsubsection:: *)
(*Specific Basis Split overrides*)


(* ::Text:: *)
(*These lists are those tensors for which, if they are featured in the appropriate splitting function, we do not split their indices.*)


$RetSplitBlacklist={};
$FrameSplitBlacklist={};


Frame31Split[expr_,OptionsPattern[]]:=Split31[expr,Fra,Fra3,Blacklist->$FrameSplitBlacklist,ExpandSelfDerivs->OptionValue[ExpandSelfDerivs]];Options[Frame31Split]={ExpandSelfDerivs->False};


Frame31Split::usage="Frame31split[expression] will replace all contracted pairs of frame basis indices with the sum the zero-zero contraction and the i-i contraction";


Ret31Split[expr_,OptionsPattern[]]:=Split31[expr,Ret,Ret3,Blacklist->$RetSplitBlacklist,ExpandSelfDerivs->OptionValue[ExpandSelfDerivs]];Options[Ret31Split]={ExpandSelfDerivs->False};


Ret31Split::usage="Ret31split[expression] will replace all contracted pairs of abstract Ret basis indices with the sum the zero-zero contraction and the i-i contraction";


SetPreferredSplit[Ret,Ret31Split];SetPreferredSplit[Fra,Frame31Split];


(* ::Text:: *)
(*An overload of one of the kronecker delta functions above, defined to be convenient for use with the retarded basis.*)


DeltaCanonicalize[DeltaName_,expr_,OptionsPattern[]]:=DeltaCanonicalize[DeltaName,expr,RetMetRules,ProbedDepth->OptionValue[ProbedDepth],IndexFilter->OptionValue[IndexFilter]];


(* ::Subsection:: *)
(*Retarded Basis Rules*)


(* ::Subsubsection:: *)
(*Tensor declarations*)


(* ::Text:: *)
(*We'll need to define the forward-pointing null vector, pointing away from the worldline, normal to spheres of constant r*)


DefTensor[norm[a],{M4},PrintAs->"\!\(\*OverscriptBox[\(n\), \(^\)]\)"];


DefTensor[x[a],{M4}];


(* ::Text:: *)
(*We'll want the kronecker delta to move between the two spatial coordinate sets.*)


DefDeltaSuite[CDelta,Ret3,Fra3,met,SpeedyButFragile->True,VanishingPDs->{PD,PDFra}];


(* ::Text:: *)
(*We're not actually using a coordinate basis, so we need manual definitions of some of the corresponding coordinate values*)


DefTensor[r[],{M4}];


(* ::Text:: *)
(*The acceleration is a fundamental value for the retarded normal coordinate system, so we need acceleration and its derivative defined:*)


DefTensor[acc[a],{M4},PrintAs->"a"];
DefTensorPerturbation[accpert[LI[o],a],acc[a],{M4},PrintAs->"a"];
DefTensor[acc1d[a],{M4},PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)a"];
DefTensorPerturbation[acc1dpert[LI[o],a],acc1d[a],{M4},PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)a"];
DefTensor[acc2d[a],{M4},PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)^2 a"];
DefTensorPerturbation[acc2dpert[LI[o],a],acc2d[a],{M4},PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)^2 a"];


(* ::Subsubsection:: *)
(*Rule declarations*)


(* ::Text:: *)
(*Edited to be consistent with the scaled coordinates throughout the computation.*)


(* ::Text:: *)
(*Normal vector rules:*)


norm/:norm[as_]norm[bs_]/;as==ChangeIndex[bs]:=0;
norm/:norm[{i_,Ret3}]norm[{-j_,-Ret3}]/;i===j:=0;
norm/:norm[{i_,Fra3}]norm[{-j_,-Fra3}]/;i===j:=0;
norm/:norm[{0,Fra}]:=1;


norm[{i,Fra3}]norm[{-i,-Fra3}]


norm/:norm[{i_,Ret3}]:=Module[{j},CDelta[Ret3,-Fra3][{i,Ret3},{-j,-Fra3}]norm[{j,Fra3}]];
norm/:norm[{-i_,-Ret3}]:=Module[{j},CDelta[-Ret3,-Fra3][{-i,-Ret3},{-j,-Fra3}]norm[{j,Fra3}]];


norm/:norm[{i_,-Ret3}]norm[{j_,-Ret3}]CDelta[Ret3,Ret3][{k_,Ret3},{l_,Ret3}]/;i==-k&&l==-j:=1;
norm/:norm[{i_,-Fra3}]norm[{j_,-Fra3}]CDelta[Fra3,Fra3][{k_,Fra3},{l_,Fra3}]/;i==-k&&l==-j:=1;
norm/:norm[{i_,Fra3}]norm[{j_,Fra3}]CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-l_,-Fra3}]/;i==k&&l==j:=1;


acc/:acc[{i_,Fra3}]CDelta[-Fra3,Fra3][ind1___,{-i_,-Fra3},ind2___]:=acc[ind1,ind2];
acc/:acc[{i_,Fra3}]CDelta[-Fra3,-Fra3][ind1___,{-i_,-Fra3},ind2___]:=acc[ind1,ind2];


acc/:acc[{i_,Fra3}]norm[{-i_,-Fra3}]:=acc[{-i,-Fra3}]norm[{i,Fra3}];


norm/:norm[{0,Ret}]:=0;


(* ::Text:: *)
(*The frame versions are simple enough that it's actually more optimal to have them replaced automatically*)


met/:met[{0,-Fra},{0,-Fra}]:=-1;
met/:met[{0,Fra},{0,Fra}]:=-1;
met/:met[{i_,-Fra3},{j_,-Fra3}]:=CDelta[-Fra3,-Fra3][{i,-Fra3},{j,-Fra3}];
met/:met[{i_,Fra3},{j_,Fra3}]:=CDelta[Fra3,Fra3][{i,Fra3},{j,Fra3}];
met/:met[{0,-Fra},{j_,-Fra3}]:=0;
met/:met[{0,Fra},{j_,Fra3}]:=0;
met/:met[{i_,-Fra3},{0,-Fra}]:=0;
met/:met[{i_,Fra3},{0,Fra}]:=0;


RetMetRules:={
met[{0,-Ret},{0,-Ret}]:>Scalar[-1-2*acc[{-i,-Fra3}]*norm[{i,Fra3}]*\[Epsilon]*r[]+acc[{-i,-Fra3}]*acc[{i,Fra3}]*\[Epsilon]^2*r[]^2
								-acc[{-i,-Fra3}]*acc[{-j,-Fra3}]norm[{i,Fra3}]norm[{j,Fra3}]*\[Epsilon]^2*r[]^2],
met[{0,Ret},{0,Ret}]:>0,
met[{i_,-Ret3},{j_,-Ret3}]:>CDelta[-Ret3,-Ret3][{i,-Ret3},{j,-Ret3}]-Module[{k,m},CDelta[-Ret3,-Fra3][{i,-Ret3},{-k,-Fra3}]CDelta[-Ret3,-Fra3][{j,-Ret3},{-m,-Fra3}]norm[{k,Fra3}]norm[{m,Fra3}]],
met[{i_,Ret3},{j_,Ret3}]:>CDelta[Ret3,Ret3][{i,Ret3},{j,Ret3}] +Module[{k,m},CDelta[Ret3,-Fra3][{i,Ret3},{-k,-Fra3}]acc[{k,Fra3}]CDelta[Ret3,-Fra3][{j,Ret3},{-m,-Fra3}]norm[{m,Fra3}]*\[Epsilon]*r[]
							 + CDelta[Ret3,-Fra3][{j,Ret3},{-m,-Fra3}]CDelta[Ret3,-Fra3][{i,Ret3},{-k,-Fra3}]norm[{k,Fra3}]acc[{m,Fra3}]*\[Epsilon]*r[]],
met[{0,-Ret},{i_,-Ret3}]:>Module[{j,k,l,m},CDelta[-Ret3,-Fra3][{i,-Ret3},{-k,-Fra3}](-norm[{k,Fra3}]-acc[{-j,-Fra3}]*norm[{k,Fra3}]norm[{j,Fra3}]*\[Epsilon]*r[])
											 + CDelta[-Ret3,Fra3][{i,-Ret3},{m,Fra3}]acc[{-m,-Fra3}]*\[Epsilon]*r[]],
met[{0,Ret},{i_,Ret3}]:>-Module[{j},CDelta[Ret3,-Fra3][{i,Ret3},-{j,Fra3}]norm[{j,Fra3}]],
met[{i_,-Ret3},{0,-Ret}]:>Module[{j,k,l,m},CDelta[-Ret3,-Fra3][{i,-Ret3},{-k,-Fra3}](-norm[{k,Fra3}]-acc[{-j,-Fra3}]*norm[{k,Fra3}]norm[{j,Fra3}]*\[Epsilon]*r[]) 
											+ CDelta[-Ret3,Fra3][{i,-Ret3},{m,Fra3}]acc[{-m,-Fra3}]*\[Epsilon]*r[]],
met[{i_,Ret3},{0,Ret}]:>-Module[{j},CDelta[Ret3,-Fra3][{i,Ret3},-{j,Fra3}]norm[{j,Fra3}]]};


RetMetRules::usage="RetMetRules is a set of rules that evaluate the 3+1 value of the metric in retarded coordinates - abstract or frame 3+1 indices, assuming flat spacetime";


RetFrameVectorRules:={
Basis[{0,-Ret},{i_,Fra3}]:>r[]acc[{i,Fra3}]*\[Epsilon],
Basis[{0,-Ret},{0,Fra}]:>Scalar[Module[{i,j},1+r[]*\[Epsilon]*acc[{-i,-Fra3}]norm[{i,Fra3}]]],
Basis[{-j_,-Ret3},{i_,Fra3}]:>CDelta[-Ret3,Fra3][{-j,-Ret3},{i,Fra3}],
Basis[{-j_,-Ret3},{0,Fra}]:>Module[{m},CDelta[-Ret3,-Fra3][{-j,-Ret3},{-m,-Fra3}]norm[{m,Fra3}]]
,
Basis[{0,Ret},{0,-Fra}]:>1,
Basis[{j_,Ret3},{i_,-Fra3}]:>CDelta[Ret3,-Fra3][{j,Ret3},{i,-Fra3}] + Module[{k,l},r[]*\[Epsilon]*CDelta[Ret3,-Fra3][{j,Ret3},{-k,-Fra3}]CDelta[-Fra3,-Fra3][{i,-Fra3},-{l,Fra3}]acc[{k,Fra3}]norm[{l,Fra3}]],
Basis[{0,Ret},{i_,-Fra3}]:>-Module[{j},CDelta[-Fra3,-Fra3][{i,-Fra3},-{j,Fra3}]norm[{j,Fra3}]],
Basis[{j_,Ret3},{0,-Fra}]:>Module[{k},-r[]*\[Epsilon]*CDelta[Ret3,-Fra3][{j,Ret3},{-k,-Fra3}]acc[{k,Fra3}]]
,
Basis[({0,Ret}|-{0,Ret}),({i_,Ret3} | -{i_,Ret3})]:>0,
Basis[({i_,Ret3} | -{i_,Ret3}),({0,Ret}|-{0,Ret})]:>0,
Basis[({0,Fra}|-{0,Fra}),({i_,Fra3} | -{i_,Fra3})]:>0,
Basis[({i_,Fra3} | -{i_,Fra3}),({0,Fra}|-{0,Fra})]:>0};


RetFrameVectorRules::usage="RetFrameVectorRules is a set of rules that evaluates the 3+1 value of the frame vectors in retarded coordinates, assuming flat spacetime";


(* ::Text:: *)
(*To simplify more efficiently, we'll insist that the two indices of the metric always appear in the same basis.*)


met/:met[{a_,basis1_},{b_,basis2_}]/;(UpIndexQ[{a,basis1}])&&(MemberQ[{Ret,-Ret,Ret3,-Ret3},basis1]&&MemberQ[{Fra,-Fra,Fra3,-Fra3},basis2]):=Module[{c},Basis[{a,basis1},{-c,-Fra}]met[{c,Fra},{b,basis2}]];
met/:met[{a_,basis1_},{b_,basis2_}]/;(UpIndexQ[{a,basis1}])&&(MemberQ[{Ret,-Ret,Ret3,-Ret3},basis2]&&MemberQ[{Fra,-Fra,Fra3,-Fra3},basis1]):=Module[{c},Basis[{b,basis2},{-c,-Fra}]met[{c,Fra},{a,basis1}]];
met/:met[{a_,basis1_},{b_,basis2_}]/;(DownIndexQ[{a,basis1}])&&(MemberQ[{Ret,-Ret,Ret3,-Ret3},basis1]&&MemberQ[{Fra,-Fra,Fra3,-Fra3},basis2]):=Module[{c},Basis[{a,basis1},{c,Fra}]met[-{c,Fra},{b,basis2}]];
met/:met[{a_,basis1_},{b_,basis2_}]/;(DownIndexQ[{a,basis1}])&&(MemberQ[{Ret,-Ret,Ret3,-Ret3},basis2]&&MemberQ[{Fra,-Fra,Fra3,-Fra3},basis1]):=Module[{c},Basis[{b,basis2},{c,Fra}]met[-{c,Fra},{a,basis1}]];


(* ::Text:: *)
(*The delta should also act as a projection:*)


CDelta/:CDelta[__][inds__]/;MemberQ[{inds},{0,(Ret|-Ret|Fra|-Fra|Ret3|-Ret3|Fra3|-Fra3)}]:=0;


(* ::Text:: *)
(*A function to apply all of the operations that we need to effectively `canonicalize' our expressions as we'd like.*)


(* ::Subsection:: *)
(*Canon Utility functions*)


ContractDeltaAcc={accpert[LI[o_],{i_,Fra3}] CDelta[-Fra3,-Fra3][{-i_,-Fra3},{-k_,-Fra3}]:>accpert[LI[o],{-k,-Fra3}],
				  accpert[LI[o_],{i_,Fra3}] CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-i_,-Fra3}]:>accpert[LI[o],{-k,-Fra3}],
				  accpert[LI[o_],{-i_,-Fra3}] CDelta[Fra3,Fra3][{i_,Fra3},{k_,Fra3}]:>accpert[LI[o],{k,Fra3}],
				  accpert[LI[o_],{-i_,-Fra3}] CDelta[-Fra3,-Fra3][{k_,Fra3},{i_,Fra3}]:>accpert[LI[o],{k,Fra3}],
				  acc1dpert[LI[o_],{i_,Fra3}] CDelta[-Fra3,-Fra3][{-i_,-Fra3},{-k_,-Fra3}]:>acc1dpert[LI[o],{-k,-Fra3}],
				  acc1dpert[LI[o_],{i_,Fra3}] CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-i_,-Fra3}]:>acc1dpert[LI[o],{-k,-Fra3}],
				  acc1dpert[LI[o_],{-i_,-Fra3}] CDelta[Fra3,Fra3][{i_,Fra3},{k_,Fra3}]:>acc1dpert[LI[o],{k,Fra3}],
				  acc1dpert[LI[o_],{-i_,-Fra3}] CDelta[-Fra3,-Fra3][{k_,Fra3},{i_,Fra3}]:>acc1dpert[LI[o],{k,Fra3}],
				  acc[{i_,Fra3}] CDelta[-Fra3,-Fra3][{-i_,-Fra3},{-k_,-Fra3}]:>acc[{-k,-Fra3}],
				  acc[{i_,Fra3}] CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-i_,-Fra3}]:>acc[{-k,-Fra3}],
				  acc[{-i_,-Fra3}] CDelta[Fra3,Fra3][{i_,Fra3},{k_,Fra3}]:>acc[{k,Fra3}],
				  acc[{-i_,-Fra3}] CDelta[-Fra3,-Fra3][{k_,Fra3},{i_,Fra3}]:>acc[{k,-Fra3}]};


RetCanon[expr_]:=SortDummies@DeltaCanonicalize[CDelta,(Expand[ContractBasis[ContractBasis[expr,Fra],Ret]]/.RetMetRules/.RetFrameVectorRules)
						//NoScalar//Expand//ContractMetric,RetMetRules,IndexFilter->{_,(Fra|-Fra3)}]/.RetMetRules/.RetFrameVectorRules


RetCanon::usage="RetCanon[expr] is a convenience function for contracting the deltas and basis vectors as appropriate, applying the 
values of the metric and frame vectors, and re-arranging kronecker deltas into a standard form";


NoScreen=0;


NoMetriconVBundle=1;


NoScreenNoMetric=2;


BasisCanon[NoScreenNoMetric][expr_]:=ToCanonical[DeltaCanonicalize[CDelta,expr]/.ContractDeltaAcc//SortDummies//GenerateNewDummies,UseMetricOnVBundle->None]//ExpandAll


BasisCanon[NoMetriconVBundle][expr_]:=ToCanonical[DeltaCanonicalize[CDelta,expr]/.ContractDeltaAcc//SortDummies//GenerateNewDummies,UseMetricOnVBundle->None]//ScreenDollarIndices//ExpandAll


BasisCanon[NoScreen][expr_]:=ToCanonical[DeltaCanonicalize[CDelta,expr]/.ContractDeltaAcc//SortDummies//GenerateNewDummies]//ExpandAll;


BasisCanon[expr_]/;!(expr===0||expr===1||expr===2):=ToCanonical[DeltaCanonicalize[CDelta,expr]/.ContractDeltaAcc//SortDummies//GenerateNewDummies]//ScreenDollarIndices//ExpandAll


BasisCanon::usage=
"BasisCanon[expr] is a convenience function for both applying the custom canonicalization of kronecker deltas and the xTensor 
canonicalize, as well as generating new dummy indices to prevent collisions
BasisCanon[NoScreen][expr] will omit the step of screening the free dollar indices. Useful if applying to sub-expressions for which the free indices are actually dummies.
BasisCanon[NoMetricOnVBundle][expr] will pass 'usemetriconvbundle->None' to the xTensor canonicalization operation, preventing the canonicalizer from raising/lowering indices or 
	commuting contraction through partial derivatives. Useful if partial derivatives are present in the expression.
BasisCanon[NoScreenNoMetric][expr] will both omit the screen step and pass 'usemetriconvbundle->None' to the xTensor canonicalizer."


(* ::Subsection:: *)
(*Tests of Basis rules*)


(met[{0,-Ret},{0,-Ret}]//BasisConvertTrace[Fra])//RetCanon


met[{0,-Ret},{0,-Ret}]//RetCanon


(met[{0,-Ret},{-i,-Ret3}]//BasisConvertTrace[Fra]//RetCanon)


met[{0,-Ret},{-i,-Ret3}]//RetCanon


met[{-i,-Ret3},{-j,-Ret3}]//BasisConvertTrace[Fra]//RetCanon


met[{-i,-Ret3},{-j,-Ret3}]//RetCanon


met[{-0,-Fra},{-a,-Fra}]Basis[{a,Fra},{-b,-Ret}]met[{b,Ret},{0,Ret}]//Ret31Split//Frame31Split//RetCanon


Basis[{-0,-Fra},{0,Ret}]//RetCanon


met[{-k,-Fra3},{-a,-Fra}]Basis[{a,Fra},{-b,-Ret}]met[{b,Ret},{0,Ret}]//Ret31Split//Frame31Split//RetCanon


Basis[{-k,-Fra3},{0,Ret}]//RetCanon


met[{-k,-Fra3},{-a,-Fra}]Basis[{a,Fra},{-b,-Ret}]met[{b,Ret},{j,Ret3}]//Ret31Split//Frame31Split//RetCanon


Basis[{-k,-Fra3},{j,Ret3}]//RetCanon


met[{i,Ret3},{a,Ret}]met[{-a,-Ret},{0,-Ret}]//Ret31Split//RetCanon//ToCanonical


met[{0,Ret},{a,Ret}]met[{-a,-Ret},{0,-Ret}]//Ret31Split//RetCanon//ToCanonical


met[{0,Ret},{a,Ret}]met[{-a,-Ret},{-i,-Ret3}]//Ret31Split//RetCanon//ToCanonical


met[{j,Ret3},{a,Ret}]met[{-a,-Ret},{-i,-Ret3}]//Ret31Split//RetCanon//ToCanonical


Basis[{-i,-Ret3},{a,Fra}]met[{-a,-Fra},{-b,-Fra}]Basis[{b,Fra},{-j,-Ret3}]//Frame31Split//RetCanon


met[{-i,-Ret3},{-j,-Ret3}]//RetCanon


Basis[{i,Ret3},{-a,-Fra}]met[{a,Fra},{b,Fra}]Basis[{-b,-Fra},{j,Ret3}]//Frame31Split//RetCanon


met[{i,Ret3},{j,Ret3}]//RetCanon


Basis[{0,-Ret},{a,Fra}]met[{-a,-Fra},{-b,-Fra}]Basis[{b,Fra},{-j,-Ret3}]//Frame31Split//RetCanon


met[{0,-Ret},{-j,-Ret3}]//RetCanon


Basis[{0,Ret},{-a,-Fra}]met[{a,Fra},{b,Fra}]Basis[{-b,-Fra},{j,Ret3}]//Frame31Split//RetCanon


met[{0,Ret},{j,Ret3}]//RetCanon


Basis[{0,-Ret},{a,Fra}]met[{-a,-Fra},{-b,-Fra}]Basis[{b,Fra},{0,-Ret}]//Frame31Split//RetCanon


met[{0,-Ret},{0,-Ret}]//RetCanon


Basis[{0,Ret},{-a,-Fra}]met[{a,Fra},{b,Fra}]Basis[{-b,-Fra},{0,Ret}]//Frame31Split//RetCanon


met[{0,Ret},{0,Ret}]//RetCanon


(* ::Subsection:: *)
(*Auxillary Basis Rules : derivatives of r[] and n[a]*)


(* ::Subsubsection:: *)
(*Rule statements*)


(* ::Text:: *)
(*I won't derive this directly, but the values I use are available from [Poisson LRR].*)


(* ::Text:: *)
(*The second of these feels silly, but I'll leave it be...*)


(*r/:PD[{-0,-Fra}][r[]]:=Scalar[-r[] \[Epsilon] acc[{-i,-Fra3}]norm[{i,Fra3}]];*)
r/:PD[{-0,-Fra}][r[]]:=Scalar[-r[]  acc[{-i,-Fra3}]norm[{i,Fra3}]];
r/:PD[{-j_,-Fra3}][r[]]:=Module[{i,k},(1 + \[Epsilon] r[]acc[{-i,-Fra3}]norm[{i,Fra3}])CDelta[-Fra3,-Fra3][-{j,Fra3},-{k,Fra3}]norm[{k,Fra3}]];
(*r/:PD[{-j_,-Fra3}][r[]]:=Module[{i,k},(1 + \[Epsilon] r[]acc[{-i,-Fra3}]norm[{i,Fra3}])CDelta[-Fra3,-Fra3][-{j,Fra3},-{k,Fra3}]norm[{k,Fra3}]];*)


(*r/:PD[{0,Fra}][r[]]:=Scalar[r[] * \[Epsilon] * acc[{-i,-Fra3}]norm[{i,Fra3}]];*)
r/:PD[{0,Fra}][r[]]:=Scalar[r[] * acc[{-i,-Fra3}]norm[{i,Fra3}]];
r/:PD[{j_,Fra3}][r[]]:=Module[{i,k},(1 + r[]*\[Epsilon]*acc[{-i,-Fra3}]norm[{i,Fra3}]) norm[{j,Fra3}]];


Unprotect[PD];
PD/:PD[{i_,Fra3}][exp_]:=Module[{j},CDelta[Fra3,Fra3][{i,Fra3},{j,Fra3}]PD[{-j,-Fra3}][exp]];
PD/:PD[{0,Fra}][exp_]:=-PD[{0,-Fra}][exp];
Protect[PD];


r/:PD[{-0,-Ret}][r[]]:=0;
r/:PD[{-j_,-Ret3}][r[]]:=Module[{i,k},CDelta[-Ret3,Fra3][{-j,-Ret3},{-i,-Fra3}]norm[{i,Fra3}]];


r/:PD[{i_,Ret3}][r[]]:=Module[{j,k},r[]*\[Epsilon]*acc[{j,Fra3}]*CDelta[Ret3,-Fra3][{i,Ret3},{-j,-Fra3}]+CDelta[Ret3,-Fra3][{i,Ret3},{-j,-Fra3}]norm[{j,Fra3}]+
									r[]*\[Epsilon]*acc[{-k,-Fra3}]*norm[{i,Ret3}]*norm[{k,Fra3}]];
r/:PD[{0,Ret}][r[]]:=-1;


(*x/:PD[{-0,-Fra}][x[{i_,Fra3}]]:=-r[]*\[Epsilon]*acc[{i,Fra3}];*)
x/:PD[{-0,-Fra}][x[{i_,Fra3}]]:=-r[] acc[{i,Fra3}];
x/:PD[{-i_,-Fra3}][x[{j_,Fra3}]]:=delta[{-i,-Fra3},{j,Fra3}] + r[]*\[Epsilon]*acc[{-j,-Fra3}]norm[{i,Fra3}];


(*norm/:PD[{0,-Fra}][norm[{i_,Fra3}]]:=-\[Epsilon] acc[{i,Fra3}] + \[Epsilon] Module[{j},acc[{-j,-Fra3}]norm[{j,Fra3}]norm[{i,Fra3}]];*)
norm/:PD[{0,-Fra}][norm[{i_,Fra3}]]:=-acc[{i,Fra3}] + Module[{j},acc[{-j,-Fra3}]norm[{j,Fra3}]norm[{i,Fra3}]];
norm/:PD[{-k_,-Fra3}][norm[{j_,Fra3}]]:=(CDelta[-Fra3,Fra3][{-k,-Fra3},{j,Fra3}]/r[] - (1/r[])Module[{i},norm[{j,Fra3}]CDelta[-Fra3,-Fra3][{-k,-Fra3},{-i,-Fra3}]norm[{i,Fra3}]]
										+\[Epsilon] acc[{j,Fra3}]norm[{-k,-Fra3}] - \[Epsilon] Module[{i,l},acc[{-l,-Fra3}]norm[{l,Fra3}]norm[{j,Fra3}]CDelta[-Fra3,-Fra3][{-k,-Fra3},{-i,-Fra3}]norm[{i,Fra3}]]);


norm/:norm[{-k_,-Fra3}]:=Module[{l},CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}]norm[{l,Fra3}]];


norm/:PD[{-0,-Ret}][norm[{i_,Fra3}]]:=0;
norm/:PD[{-j_,-Ret3}][norm[{i_,Fra3}]]:=Module[{k},CDelta[-Ret3,Fra3][{-j,-Ret3},{i,Fra3}]/r[]-(CDelta[-Ret3,-Fra3][{-j,-Ret3},-{k,Fra3}]*norm[{i,Fra3}]*norm[{k,Fra3}])/r[]];


\[Epsilon]/:PD[__][\[Epsilon]]:=0;
acc/:PD[-{0,Ret}][acc[{i_,Fra3}]]:=acc1d[{i,Fra3}];
acc/:PD[-{0,Ret}][acc[{-i_,-Fra3}]]:=acc1d[{-i,-Fra3}];
acc/:PD[-{0,Fra}][acc[{i_,Fra3}]]:=acc1d[{i,Fra3}];
acc/:PD[-{0,Fra}][acc[{-i_,-Fra3}]]:=acc1d[{-i,-Fra3}];


Unprotect[PD];
PD/:PD[-{0,Fra}][acc1d[{i_,Fra3}]]:=Module[{j},acc2d[{i,Fra3}]-acc[{i,Fra3}]acc[{-j,-Fra3}]acc[{j,Fra3}]];
PD/:PD[-{0,Fra}][acc1d[{-i_,-Fra3}]]:=Module[{j},acc2d[{-i,-Fra3}]-acc[{-i,-Fra3}]acc[{-j,-Fra3}]acc[{j,Fra3}]];
PD/:PD[{-l_,-Fra3}][acc1d[{k_,Fra3}]]:=Module[{i,j},-\[Epsilon]( acc2d[{k,Fra3}]norm[{i,Fra3}]CDelta[-Fra3,-Fra3][{-l,-Fra3},{-i,-Fra3}]
															- acc[{k,Fra3}] acc[{-j,-Fra3}]acc[{j,Fra3}] norm[{i,Fra3}]CDelta[-Fra3,-Fra3][{-l,-Fra3},{-i,-Fra3}] )];
PD/:PD[{-l_,-Fra3}][acc1d[{-k_,-Fra3}]]:=Module[{i,j},-\[Epsilon]( acc1d[{-k,-Fra3}]norm[{i,Fra3}]CDelta[-Fra3,-Fra3][{-l,-Fra3},{-i,-Fra3}] 
															- acc[{-k,-Fra3}] acc[{-j,-Fra3}]acc[{j,Fra3}] norm[{i,Fra3}]CDelta[-Fra3,-Fra3][{-l,-Fra3},{-i,-Fra3}])];
Protect[PD];


accpert/:PD[-{0,Ret}][accpert[LI[n_],{i_,Fra3}]]:=acc1dpert[LI[n],{i,Fra3}];
accpert/:PD[-{0,Ret}][accpert[LI[n_],-{i_,Fra3}]]:=acc1dpert[LI[n],-{i,Fra3}];


acc/:PD[-{l_,Ret3}][acc[-{k_,Fra3}]]:=0;
acc/:PD[-{l_,Ret3}][acc[{k_,Fra3}]]:=0;
acc1d/:PD[-{l_,Ret3}][acc1d[__]]:=0;
acc2d/:PD[-{l_,Ret3}][acc2d[__]]:=0;


acc/:acc[{0,Fra}]:=0;


acc/:PD[{_, Ret3|-Ret3}][acc[{a_,Fra}]]:=0;
acc/:PD[{_,Ret3|-Ret3}][acc[{-a_,-Fra}]]:=0;
acc/:PD[{_, Ret3|-Ret3}][acc[{a_,Fra3}]]:=0;
acc/:PD[{_,Ret3|-Ret3}][acc[{-a_,-Fra3}]]:=0;


(Basis[{-i,-Ret3},{a,Fra}]PD[{-a,-Fra}][acc1d[{j,Fra3}]]//Frame31Split)/.RetFrameVectorRules


acc/:PD[{-l_,-Fra3}][acc[{k_,Fra3}]]:=Module[{i},-\[Epsilon] acc1d[{k,Fra3}]norm[{i,Fra3}]CDelta[-Fra3,-Fra3][{-l,-Fra3},{-i,-Fra3}]];
acc/:PD[{-l_,-Fra3}][acc[{-k_,-Fra3}]]:=Module[{i},-\[Epsilon] acc1d[{-k,-Fra3}]norm[{i,Fra3}]CDelta[-Fra3,-Fra3][{-l,-Fra3},{-i,-Fra3}]];


acc1d/:acc1d[a_?UpIndexQ]acc[u1_][b_]/;ChangeIndex[b]===a:=acc1d[ChangeIndex[a]]acc[a];


acc1d[{-i_,-Fra3}]:=Module[{j},acc1d[{j,Fra3}]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-i,-Fra3}]];


acc[{0,-Fra}]:=-acc[{0,Fra}];
acc1d[{0,-Fra}]:=-acc1d[{0,Fra}];
acc2d[{0,-Fra}]:=-acc2d[{0,Fra}];


acc1d[{0,Fra}]:=Module[{i},acc[-{i,Fra3}]acc[{i,Fra3}]];


CD[__][\[Epsilon]]:=0;


(* ::Subsubsection:: *)
(*Auxillary rule tests*)


Basis[{-0,-Ret},{a,Fra}]PD[{-a,-Fra}][r[]]//Frame31Split//RetCanon//ToCanonical


((Basis[{-i,-Ret3},{a,Fra}]PD[{-a,-Fra}][r[]])//Frame31Split)//RetCanon//ToCanonical


(met[{i,Ret3},{a,Ret}]PD[{-a,-Ret}][r[]]//Ret31Split)/.RetMetRules//ToCanonical


Expand[(met[{0,Ret},{a,Ret}]PD[{-a,-Ret}][r[]]//Ret31Split)/.RetMetRules]


(Expand[PD[{0,-Fra}][x[{i,Fra3}]/r[]]])/.x[{i_,Fra3}]:>(r[]norm[{i,Fra3}])


Expand[PD[{-j,-Fra3}][x[{i,Fra3}]/r[]]/.x[{i_,Fra3}]:>(r[]norm[{i,Fra3}])]


Basis[{-j,-Ret3},{0,Fra}]


PD[{-0,-Fra}][norm[{i,Ret3}]]//ExpandAll


PD[-{0,Ret}][(met[-{i,Ret3},-{a,Ret}]norm[{a,Ret}])//Ret31Split]/.RetMetRules


PD[-{0,Ret}][(met[-{0,Ret3},-{a,Ret}]norm[{a,Ret}])//Ret31Split]/.RetMetRules


ToCanonical[PD[-{j,Ret3}][(met[-{i,Ret3},-{a,Ret}]norm[{a,Ret}])//Ret31Split]/.RetMetRules//Expand,UseMetricOnVBundle->None]


PD[-{j,Ret3}][(met[-{0,Ret3},-{a,Ret}]norm[{a,Ret}])//Ret31Split]/.RetMetRules//Expand


(* ::Subsection:: *)
(*Pre-computed Christoffel components*)


AbstractToBasis[basis_][expr_]:=expr//.{tens_[first___,a_?AbstractIndexQ,last___]/;!(tens===List)&&!(tens===Times)&&UpIndexQ[a]:>tens[first,{a,basis},last],
tens_[first___,-a_?AbstractIndexQ,last___]/;!(tens===List):>tens[first,-{a,basis},last]}


ChristoffelPD/:ChristoffelPD[__]:=0


TorsionPD/:TorsionPD[__]:=0


CreateDirectory["~/.ScalarSelfForceCache/"];


ClearAll[ChristoffelPreComputeFraRuleListPartial];ClearAll[ChristoffelPreComputeFraRuleList];


UnScalefromTempDerivs[expr_]:=(((expr//.{PDTemp[{0,-Fra}][ex_]:>(1/\[Epsilon]) PDpTemp[{0,-Fra}][ex], CD[{0,-Fra}][ex_]:>(1/\[Epsilon]) CDpTemp[{0,-Fra}][ex],
									PDTemp[{0,-Ret}][ex_]:>(1/\[Epsilon]) PDpTemp[{0,-Ret}][ex], CD[{0,-Ret}][ex_]:>(1/\[Epsilon]) CDpTemp[{0,-Ret}][ex],
									PDTemp[{0,Fra}][ex_]:>(1/\[Epsilon]) PDpTemp[{0,Fra}][ex],CDTemp[{0,Fra}][ex_]:>(1/\[Epsilon]) CDpTemp[{0,Fra}][ex],
								    PDTemp[{0,Ret}][ex_]:>(1/\[Epsilon]) PDpTemp[{0,Ret}][ex],CDTemp[{0,Ret}][ex_]:>(1/\[Epsilon]) CDpTemp[{0,Ret}][ex]}))
									//.{CDpTemp->CDTemp,PDpTemp->PDTemp});


ScalefromTempDerivs[expr_]:=((expr//.{PDTemp[{0,-Fra}][ex_]:>\[Epsilon] PD[{0,-Fra}][ex],CDTemp[{0,-Fra}][ex_]:>\[Epsilon] CD[{0,-Fra}][ex],
								 PDTemp[{0,-Ret}][ex_]:>\[Epsilon] PD[{0,-Ret}][ex],CDTemp[{0,-Ret}][ex_]:>\[Epsilon] CD[{0,-Ret}][ex],
								 PDTemp[{0,Fra}][ex_]:>\[Epsilon] PD[{0,Fra}][ex],CDTemp[{0,Fra}][ex_]:>\[Epsilon] CD[{0,Fra}][ex],
								 PDTemp[{0,Ret}][ex_]:>\[Epsilon] PD[{0,Ret}][ex],CDTemp[{0,Ret}][ex_]:>\[Epsilon] CD[{0,Ret}][ex]}));


(CheckpointGenerate3p1[ChristoffelCD[{a,Fra},{-b,-Fra},{-c,-Fra}]][ChristoffelPreComputeFraRuleListPartial]["~/.ScalarSelfForceCache/ChristoffelPreComputeFraRuleListEMPart.mx"][\
			((#//ChristoffelToGradMetric//AbstractToBasis[Ret]//Frame31Split)/.RetMetRules//Ret31Split//ScaleDerivs//RetCanon//BasisCanon[NoScreen]//GenerateNewDummies)&]);//Timing


(CheckpointGenerate3p1[ChristoffelCD[{a,Fra},{-b,-Fra},{-c,-Fra}],UpAndDownInds->True][ChristoffelPreComputeFraRuleList]["~/.ScalarSelfForceCache/ChristoffelPreComputeFraRuleListEM.mx"][\
			((#/.{ChristoffelCD[a_,b_,c_]:>Module[{d,e,f},((met[a,-{d,Fra}]met[b,{e,Fra}]met[c,{f,Fra}]ChristoffelCD[{d,Fra},-{e,Fra},-{f,Fra}]))]}
					//Frame31Split)/.RetFrameVectorRules/.ChristoffelPreComputeFraRuleListPartial//Expand//RetCanon//GenerateNewDummies)&]);//Timing


ClearAll[ChristoffelPreComputeRetRuleListPartial];ClearAll[ChristoffelPreComputeRetRuleList];


ChristoffelPreComputeFra[expr_]:=(expr/.ChristoffelPreComputeFraRuleList)//Expand;


(CheckpointGenerate3p1[ChristoffelCD[{a,Ret},{-b,-Ret},{-c,-Ret}]][ChristoffelPreComputeRetRuleListPartial]["~/.ScalarSelfForceCache/ChristoffelPreComputeRetRuleListEMPart.mx"][\
			(#//ChristoffelToGradMetric//AbstractToBasis[Ret]//Ret31Split//ScaleDerivs//RetCanon//BasisCanon[NoScreen]//GenerateNewDummies)&]);//Timing


(CheckpointGenerate3p1[ChristoffelCD[{a,Ret},{-b,-Ret},{-c,-Ret}],UpAndDownInds->True][ChristoffelPreComputeRetRuleList]["~/.ScalarSelfForceCache/ChristoffelPreComputeRetRuleListEM.mx"][\
			(((#/.{ChristoffelCD[a_,b_,c_]:>Module[{d,e,f},(met[a,-{d,Ret}]met[b,{e,Ret}]met[c,{f,Ret}]ChristoffelCD[{d,Ret},-{e,Ret},-{f,Ret}])]})
				//Ret31Split)/.RetFrameVectorRules/.RetMetRules/.ChristoffelPreComputeRetRuleListPartial//Expand//BasisCanon[NoScreen]//GenerateNewDummies)&]);//Timing


ChristoffelPreCompute[expr_]:=(expr/.ChristoffelPreComputeFraRuleList/.ChristoffelPreComputeRetRuleList)//Expand;


PDsToRet[tenspattern_][expr_]:=expr//.{PD[{-i_,-Fra3}][junk__]/;MatchQ[junk,tenspattern]:>Module[{a},(Basis[-{i,Fra3},{a,Ret}]PD[-{a,Ret}][junk]//Ret31Split)/.RetFrameVectorRules//ExpandAll],
									   PD[{0,-Fra}][junk__]/;MatchQ[junk,tenspattern]:>Module[{a},(Basis[-{0,Fra},{a,Ret}]PD[-{a,Ret}][junk]//Ret31Split)/.RetFrameVectorRules//ExpandAll],
									   PD[{-i_,-Fra3}][junk__]/;MatchQ[junk,tenspattern]:>Module[{a},(Basis[-{i,Fra3},{a,Ret}]PD[-{a,Ret}][junk]//Ret31Split)/.RetFrameVectorRules//ExpandAll],
									   PD[{0,-Fra}][junk__]/;MatchQ[junk,tenspattern]:>Module[{a},(Basis[-{0,Fra},{a,Ret}]PD[-{a,Ret}][junk]//Ret31Split)/.RetFrameVectorRules//ExpandAll]};


(* ::Text:: *)
(*Specifically , This function computes the residual in converting a tensor (specified in the arguments) to a partial derivative (include a sign for the reverse conversion. the input should have separated the basis vectors out from the covariant derivative already (this notation is precisely what I mean by a covariant derivative anyway. I think there is some code underlying xTensor that assumes otherwise, but I'll do my best to remove any automatic functions that assume the wrong form...*)


ConvertToFrame[TensPatt_][expr_]:=ConvertToBasis[TensPatt][Fra][expr];


DefTensor[PDBasis[a,b,c],{M4},PrintAs->"\[PartialD]e"];


PDTemp[__][\[Epsilon]]:=0;


ClearAll[PDBasisRule1];ClearAll[PDBasisRule2];ClearAll[PDBasisRule3];ClearAll[PDBasisRule4];


PDBasis[{k,Fra3},{-0,-Ret},{-0,-Fra}]/.{PDBasis[{a_,bas1_},{b_,bas2_},{c_,bas3_}]:>PDTemp[{a,bas1}][(Basis[{b,bas2},{c,bas3}]//Frame31Split)/.RetFrameVectorRules//NoScalar]}//.fromPDTemp//ExpandAll


PDBasis[{0,Fra},{0,-Ret},{0,-Fra}]/.{PDBasis[{a_,bas1_},{b_,bas2_},{c_,bas3_}]:>PDTemp[{a,bas1}][(Basis[{b,bas2},{c,bas3}]//Frame31Split)/.RetFrameVectorRules]}


((PDBasis[{k,Fra3},{0,-Ret},{0,-Fra}]/.{PDBasis[{a_,bas1_},{b_,bas2_},{c_,bas3_}]:>PDTemp[{a,bas1}][(Basis[{b,bas2},{c,bas3}]//Frame31Split)/.RetFrameVectorRules]})
	//ScalefromTempDerivs)//.fromPDTemp//ExpandAll


((PDBasis[{0,Fra},{0,-Ret},{0,-Fra}]/.{PDBasis[{a_,bas1_},{b_,bas2_},{c_,bas3_}]:>PDTemp[{a,bas1}][(Basis[{b,bas2},{c,bas3}]//Frame31Split)/.RetFrameVectorRules]})
							//ScalefromTempDerivs//.fromPDTemp//NoScalar//ExpandAll//BasisCanon[NoScreenNoMetric])


CheckpointGenerate3p1[PDBasis[{a,Fra},{b,Ret},{c,Fra}],UpAndDownInds->True][PDBasisRule1]["~/.ScalarSelfForceCache/PDBasisRule1.mx"][
				((((#/.{PDBasis[{a_,bas1_},{b_,bas2_},{c_,bas3_}]:>PDTemp[{a,bas1}][(Basis[{b,bas2},{c,bas3}]//Frame31Split)/.RetFrameVectorRules]})
						)//ScalefromTempDerivs)//.fromPDTemp//NoScalar//ExpandAll//BasisCanon[NoScreenNoMetric])&];


CheckpointGenerate3p1[PDBasis[{a,Ret},{b,Ret},{c,Fra}],UpAndDownInds->True][PDBasisRule2]["~/.ScalarSelfForceCache/PDBasisRule2.mx"][\
				((((#/.{PDBasis[{a_,bas1_},{b_,bas2_},{c_,bas3_}]:>PDTemp[{a,bas1}][(Basis[{b,bas2},{c,bas3}]//Frame31Split)//RetCanon//Expand]}))
							//ScalefromTempDerivs)//.fromPDTemp//NoScalar//BasisCanon[NoScreenNoMetric])&];


CheckpointGenerate3p1[PDBasis[{a,Fra},{b,Fra},{c,Ret}],UpAndDownInds->True][PDBasisRule3]["~/.ScalarSelfForceCache/PDBasisRule3.mx"][\
				((((#/.{PDBasis[{a_,bas1_},{b_,bas2_},{c_,bas3_}]:>PDTemp[{a,bas1}][(Basis[{b,bas2},{c,bas3}]//Frame31Split)//RetCanon//Expand]}))
							//ScalefromTempDerivs)//.fromPDTemp//NoScalar//BasisCanon[NoScreenNoMetric])&];


CheckpointGenerate3p1[PDBasis[{a,Ret},{b,Fra},{c,Ret}],UpAndDownInds->True][PDBasisRule4]["~/.ScalarSelfForceCache/PDBasisRule4.mx"][\
				((((#/.{PDBasis[{a_,bas1_},{b_,bas2_},{c_,bas3_}]:>PDTemp[{a,bas1}][(Basis[{b,bas2},{c,bas3}]//Frame31Split)//RetCanon//Expand]}))
							//ScalefromTempDerivs)//.fromPDTemp//NoScalar//BasisCanon[NoScreenNoMetric])&];


PDBasisRule=PDBasisRule1~Join~PDBasisRule2~Join~PDBasisRule3~Join~PDBasisRule4;


(* ::Subsection:: *)
(*Partial and covariant derivatives for the scaled curvilinear coordinates*)


(* ::Subsubsection:: *)
(*Generation of the appropriate effective christoffel symbols*)


(* ::Text:: *)
(*xTensor assumes that the covariant derivative of a basis element vanishes, which isn't the case for the Retarded normal coordinates that we use, so partial derivatives of tensors in terms of frame indices should be converted to covariant derivatives of frame-index tensors via the following utilities*)


Unprotect[Basis];Basis/:Basis[first1___,{a_,Ret},last1___]Basis[first2___,{-a_,-Ret},last2___]:=Basis[first1,first2,last1,last2];Protect[Basis];


Unprotect[Basis];Basis/:Basis[first1___,{a_,Fra},last1___]Basis[first2___,{-a_,-Fra},last2___]:=Basis[first1,first2,last1,last2];Protect[Basis];


BasisChristoffel[Ret]:=ChristoffelCD;


ClearAll[BasisChristoffelFraRules]


DefTensor[BasisTemp[a,b],{M4}];


CheckpointGenerate3p1[BasisChristoffel[Fra][{a,Fra},{-b,-Fra},{-c,-Fra}]][BasisChristoffelFraRules]["~/.ScalarSelfForceCache/BasisChristoffelFra.mx"][\
((((#/.{BasisChristoffel[Fra][a_,b_,c_]:>-(-Basis[b,{d,Ret}]Basis[c,{e,Ret}]Basis[{-f,-Ret},a]ChristoffelCD[{f,Ret},{-d,-Ret},{-e,-Ret}]
											+Basis[b,{d,Ret}]Basis[c,{e,Ret}]PDBasis[{-d,-Ret},{-e,-Ret},a])})
													//Ret31Split)/.RetFrameVectorRules/.PDBasisRule)//ChristoffelPreCompute//ExpandAll//NoScalar
														//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&]


(* ::Text:: *)
(*Note: here we need to be careful, as the derivatives are assumed to already be scaled differently for 0 and i components. The best thing to do is to remove the scaling, then replace it.*)


(* ::Text:: *)
(*TODO: bring the ScaleDerivs and UnscaleDerivs to all places in code where they should be.*)


(* ::Text:: *)
(*A couple of quick convenience functions:*)


(* ::Subsubsection::Closed:: *)
(*Functions for use with the scaled partials and covariants*)


UnScaleDerivs[expr_]:=((expr//.{PD[{0,-Fra}][ex_]:>(1/\[Epsilon]) PDTemp[{0,-Fra}][ex],CD[{0,-Fra}][ex_]:>(1/\[Epsilon]) CDTemp[{0,-Fra}][ex],
 							 PD[{0,-Ret}][ex_]:>(1/\[Epsilon]) PDTemp[{0,-Ret}][ex],CD[{0,-Ret}][ex_]:>(1/\[Epsilon]) CDTemp[{0,-Ret}][ex]})//ExpandAll)//.{CDTemp->CD,PDTemp->PD};


ScaleDerivs[expr_]:=((expr//.{PD[{0,-Fra}][ex_]:>\[Epsilon] PDTemp[{0,-Fra}][ex],CD[{0,-Fra}][ex_]:>\[Epsilon] CDTemp[{0,-Fra}][ex],
 							 PD[{0,-Ret}][ex_]:>\[Epsilon] PDTemp[{0,-Ret}][ex],CD[{0,-Ret}][ex_]:>\[Epsilon] CDTemp[{0,-Ret}][ex]})//ExpandAll)//.{CDTemp->CD,PDTemp->PD};


(* ::Text:: *)
(*Overwriting the generic form, due to specific needs and the inability for the generic form to handle mutliple derivatives*)


BasisChangeCovD[expr_]/;MatchQ[expr/.toCDTemp,CDTemp[___][tens_[inds___]]]:=Module[{CDTempForm=expr//.toCDTemp,CDInds,fullinds,abstInds,forwardMap,backwardMap,ii=1},
	fullinds=(CDTempForm/.{CDTemp[A___][_]:>{A}})~Join~(CDTempForm/.{CDTemp[___][tens_[LI[o_]inds___]]:>{inds},CDTemp[___][tens_[inds___]]:>{inds}});
	abstInds=UniqueIndex[Form4[#[[2]]]] &/@fullinds;
	forwardMap=(fullinds[[#]]/;(ii==#)&&(IntegerQ[ii++])->abstInds[[#]])&/@Range[Length[fullinds]];
	backwardMap=(abstInds[[#]]->fullinds[[#]])&/@Range[Length[fullinds]];
	Return[(ChangeCovD[expr/.forwardMap]//ExpandAll)/.{ChristoffelCD[inds__]:>BasisChristoffel[Fra][inds]}
		/.backwardMap];
];


BasisChangeCovD[expr_,d1_,d2_]/;MatchQ[expr/.toPDTemp,PDTemp[___][tens_[inds___]]]&&d1===PD&&d2===CD:=Module[{PDTempForm=expr//.toPDTemp,fullinds,abstInds,forwardMap,backwardMap,ii=1},
	fullinds=(PDTempForm/.{PDTemp[A___][_]:>{A}})~Join~(PDTempForm/.{PDTemp[___][tens_[LI[o_],inds___]]:>{inds}}/.{PDTemp[___][tens_[inds___]]:>{inds}});
	abstInds=UniqueIndex[Form4[#[[2]]]] &/@fullinds;
	forwardMap=(fullinds[[#]]/;(ii==#)&&(IntegerQ[ii++])->abstInds[[#]])&/@Range[Length[fullinds]];
	backwardMap=(abstInds[[#]]->fullinds[[#]])&/@Range[Length[fullinds]];
	Return[ChangeCovD[expr/.forwardMap,PD,CD]/.{ChristoffelCD[inds__]:>BasisChristoffel[Fra][inds]}
		/.backwardMap];
];


ScaledFramePDtoCD[expr_]:=(((ChangeCovD[expr//UnScaleDerivs,PD,CD]//Expand//AbstractToBasis[Fra]//SeparateBasisForce[Fra]
					//Expand//Frame31Split//ScaleDerivs)/.PDBasisRule//ExpandAll)
					//.{exp_*BasisChristoffel[Fra][inds__]:>exp*((BasisChristoffel[Fra][inds]/.BasisChristoffelFraRules)//GenerateNewDummies),
						exp_*PD[pds__][BasisChristoffel[Fra][inds__]]:>((exp*PD[pds][((BasisChristoffel[Fra][inds]/.BasisChristoffelFraRules)//GenerateNewDummies)])/.fromPDTemp)}
					/.BasisChristoffelFraRules/.RetFrameVectorRules//NoScalar//ExpandAll//BasisCanon[NoScreenNoMetric]);
ScaledFrameCDtoPD[expr_]:=(((ChangeCovD[expr//UnScaleDerivs,CD,PD]//Expand//AbstractToBasis[Fra]//SeparateBasisForce[Fra]
					//Expand//Frame31Split//ScaleDerivs)/.PDBasisRule//ExpandAll)
					//.{exp_*BasisChristoffel[Fra][inds__]:>exp*((BasisChristoffel[Fra][inds]/.BasisChristoffelFraRules)//GenerateNewDummies),
						exp_*PD[pds__][BasisChristoffel[Fra][inds__]]:>exp*PD[pds][((BasisChristoffel[Fra][inds]/.BasisChristoffelFraRules)//GenerateNewDummies)]}
					/.BasisChristoffelFraRules/.RetFrameVectorRules//NoScalar//ExpandAll//BasisCanon[NoScreenNoMetric]);


FramePDtoCD[expr_]:=(((ChangeCovD[expr,PD,CD]//Expand//AbstractToBasis[Fra]//SeparateBasisForce[Fra]
					//Expand//Frame31Split)/.PDBasisRule//ExpandAll)
					//.{exp_*BasisChristoffel[Fra][inds__]:>exp*((BasisChristoffel[Fra][inds]/.BasisChristoffelFraRules)//GenerateNewDummies),
						exp_*PD[pds__][BasisChristoffel[Fra][inds__]]:>((exp*PD[pds][((BasisChristoffel[Fra][inds]/.BasisChristoffelFraRules)//GenerateNewDummies)])/.fromPDTemp)}
					/.BasisChristoffelFraRules/.RetFrameVectorRules//NoScalar//ExpandAll//BasisCanon[NoScreenNoMetric]);
FrameCDtoPD[expr_]:=(((ChangeCovD[expr,CD,PD]//Expand//AbstractToBasis[Fra]//SeparateBasisForce[Fra]
					//Expand//Frame31Split)/.PDBasisRule//ExpandAll)
					//.{exp_*BasisChristoffel[Fra][inds__]:>exp*((BasisChristoffel[Fra][inds]/.BasisChristoffelFraRules)//GenerateNewDummies),
						exp_*PD[pds__][BasisChristoffel[Fra][inds__]]:>exp*PD[pds][((BasisChristoffel[Fra][inds]/.BasisChristoffelFraRules)//GenerateNewDummies)]}
					/.BasisChristoffelFraRules/.RetFrameVectorRules//NoScalar//ExpandAll//BasisCanon[NoScreenNoMetric]);


(* ::Subsubsection:: *)
(*Rule tests*)


DefTensor[Trial[a,b],{M4},PrintAs->"T"];


((ChangeCovD[CD[{0,-Fra}][CD[{0,-Fra}][Trial[{0,Fra},{0,Fra}]]]//UnScaleDerivs,CD,PD]//AbstractToBasis[Fra]//Expand//Frame31Split//ScaleDerivs)/.PDBasisRule
//.{exp_*BasisChristoffel[Fra][inds__]:>exp*((BasisChristoffel[Fra][inds]/.BasisChristoffelFraRules)//GenerateNewDummies),
						exp_*PD[pds__][BasisChristoffel[Fra][inds__]]:>exp*PD[pds][((BasisChristoffel[Fra][inds]/.BasisChristoffelFraRules)//GenerateNewDummies)]})/.BasisChristoffelFraRules//BasisCanon[NoMetriconVBundle]


DefTensor[Trial2[a,b],{M4},PrintAs->"T"];


TrialRules={Trial[{0,-Fra},{0,Fra},{0,Fra}]->(CD[{0,-Fra}][Trial2[{0,Fra},{0,Fra}]]//ScaledFrameCDtoPD),
			Trial[{0,-Fra},{0,Fra},{i_,Fra3}]->(CD[{0,-Fra}][Trial2[{0,Fra},{i,Fra3}]]//ScaledFrameCDtoPD),
			Trial[{0,-Fra},{i_,Fra3},{0,Fra}]->(CD[{0,-Fra}][Trial2[{i,Fra3},{0,Fra}]]//ScaledFrameCDtoPD),
			Trial[{-i_,-Fra3},{0,Fra},{0,Fra}]->(CD[{-i,-Fra3}][Trial2[{0,Fra},{0,Fra}]]//ScaledFrameCDtoPD)};


CD[{-i,-Fra3}][Trial2[{0,Fra},{0,Fra}]]//ScaledFrameCDtoPD


(CD[{0,-Fra}][Trial[{0,-Fra},{0,Fra},{0,Fra}]]//ScaledFrameCDtoPD)/.TrialRules//Expand//BasisCanon[NoMetriconVBundle]


CD[{0,-Fra}][CD[{0,-Fra}][Trial[{0,Fra},{0,Fra}]]]//ScaledFrameCDtoPD//BasisCanon[NoMetriconVBundle];


(* ::Text:: *)
(*These last two being equal is a good proof of concept that the multiple derivatives are working as expected.*)
