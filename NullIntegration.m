(* ::Package:: *)

(* ::Subsection:: *)
(*Integration*)


(* ::Subsubsection:: *)
(*Integration definitions*)


IntNull/:Tex[IntNull[expr_]]:="\\int d^3 x"<>Tex[expr];


DefInertHead[IntNull,LinearQ->True,ContractThrough->{delta},PrintAs->"\[Integral]\!\(\*SuperscriptBox[\(d\), \(3\)]\)x"];
DefInertHead[SIntNull,LinearQ->True,ContractThrough->{delta},PrintAs->"\[ContourIntegral]dA"];


DefTensor[R[],{M4},PrintAs->"R"];


BasisChangeCovD[IntNull[expr_]]:=IntNull[BasisChangeCovD[expr]]


(* ::Subsubsection:: *)
(*Integration Rules*)


CommuteThroughNullInt={};


CommuteThroughNullIntScalar={};


CommuteThroughNullIntConst={};


IntegrateByPartsList={};


IsIntNullIndependent[expr__]:=Module[{CDTempForm=expr//.toCDTemp,inds,tensinds},
	If[MatchQ[expr,(tens_[])^n_/;MemberQ[CommuteThroughNullIntScalar,tens]]
			||MatchQ[expr,(tens_[])/;MemberQ[CommuteThroughNullIntScalar,tens]],
			Return[True];];
	If[MatchQ[expr,cons_^n_/;MemberQ[CommuteThroughNullIntConst,cons]]
			||MatchQ[expr,cons_/;MemberQ[CommuteThroughNullIntConst,cons]],
		Return[True];];
	If[Or@@(MatchQ[CDTempForm,(CDTemp[___][#[___]] | #[___])]&/@CommuteThroughNullInt),
		inds=(CDTempForm/.{CDTemp[A___][tens__[___]]:>{A},exp_/;FreeQ[CDTemp,exp]:>{}}) ~Join~
			 (CDTempForm/.{CDTemp[___][tens__[LI[o_],A___]]:>{A},
								CDTemp[___][tens__[A___]]:>{A},
							tens_[LI[o_],A___]:>{A},
							tens_[A___]:>{A}});
		Return[And@@((Length[#]==2 && MemberQ[{Fra,-Fra,Fra3,-Fra3},#[[2]]])&/@inds)]];
	Return[False];
];


CommuteNullInt[expr_]:=expr//.{IntNull[expr1_ expr2_]/;IsIntNullIndependent[expr1]:>expr1 IntNull[expr2],
							  SIntNull[expr1_ expr2_]/;IsIntNullIndependent[expr1]:>expr1 SIntNull[expr2]};


(* ::Text:: *)
(*Let's try making the new version automatic just to see?*)
(*TODO:: evaluate if we can merge these rules to a single set of auto rules*)


IsIntNullIndependent[ChargeCurrent[{0,Fra}]]


IntNull/:IntNull[expr1_ expr2_]/;IsIntNullIndependent[expr1]:=expr1 IntNull[expr2];
SIntNull/:SIntNull[expr1_ expr2_]/;IsIntNullIndependent[expr1]:=expr1 SIntNull[expr2];


NullIntparts={IntNull[PD[{-k_,-Fra3}][tens_]]/;FreeQ[tens,(Ret|Ret3)]&&!(And@@(FreeQ[tens,#]&/@IntegrateByPartsList)):>
									(Module[{l},-IntNull[CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}] Ns[{l,Fra3}] \[Epsilon] PD[{0,-Ret}][tens]] 
									-\[Epsilon]  acc[{-k,-Fra3}]IntNull[tens] + (*-2*) SIntNull[CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}]Ns[{l,Fra3}]Scalar[1 + \[Epsilon] r[] acc[{-i,-Fra3}]Ns[{i,Fra3}]]tens]]/.nstoNsrule),
			  HoldPattern[IntNull[others_*PD[{-k_,-Fra3}][tens_]]]/;(*Print[PD[{0,-Ret}][others]]\[Equal]Null&&Print[others]\[Equal]Null&&*)FreeQ[tens,(Ret|Ret3)]&&FreeQ[others,(Ret|Ret3)]&&!(And@@(FreeQ[tens,#]&/@IntegrateByPartsList)):>
									(Module[{l},-IntNull[tens * PD[{-k,-Fra3}][others]]-IntNull[CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}] Ns[{l,Fra3}] \[Epsilon] others PD[{0,-Ret}][tens]] 
									-\[Epsilon] acc[{-k,-Fra3}]IntNull[others*tens] + (*-2*) SIntNull[CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}]Ns[{l,Fra3}]Scalar[1 + \[Epsilon] r[] acc[{-i,-Fra3}]Ns[{i,Fra3}]]others*tens]]/.nstoNsrule),
			  HoldPattern[IntNull[PD[{0,-Ret}][tens_[inds___]]*exp_]]/;MemberQ[IntegrateByPartsList,tens]:>
															((PD[{0,-Fra}][IntNull[tens[inds] exp]] - IntNull[tens[inds] PD[{0,-Ret}][exp]])/.nstoNsrule),
			  HoldPattern[IntNull[PD[{0,-Ret}][PD[{0,-Ret}][tens_[inds___]]]*exp_]]/;MemberQ[IntegrateByPartsList,tens]:>
															((PD[{0,-Fra}][IntNull[PD[{0,-Ret}][tens[inds]] exp]] - IntNull[PD[{0,-Ret}][tens[inds]] PD[{0,-Ret}][exp]])/.nstoNsrule),
			  HoldPattern[IntNull[PD[{0,-Ret}][tens_[inds___]]]]/;MemberQ[IntegrateByPartsList,tens]:>(PD[{0,-Fra}][IntNull[tens[inds]]]/.nstoNsrule),
			  HoldPattern[IntNull[PD[{0,-Ret}][PD[{0,-Ret}][tens_[inds___]]]]]/;MemberQ[IntegrateByPartsList,tens]:>(PD[{0,-Fra}][IntNull[PD[{0,-Ret}][tens[inds]]]]/.nstoNsrule)};


(* ::Subsubsection:: *)
(*Retarded basis specific utilities*)


ToRettauFrameiderivs[expr_]:=Module[{},
	Return[expr//.{PD[{0,-Fra}][ex_]:>Module[{j},(1/Scalar[1 + \[Epsilon] r[] acc[{-j,-Fra3}]norm[{j,Fra3}]]) (PD[{0,-Ret}][ex] - \[Epsilon] r[] acc[{j,Fra3}] PD[{-j,-Fra3}][ex])],
					PD[{-k_,-Ret3}][ex_]:>Module[{j,l,m},CDelta[-Ret3,Fra3][{-k,-Ret3},{j,Fra3}]PD[{-j,-Fra3}][ex]
										  + (1/Scalar[1 + \[Epsilon] r[] acc[{-j,-Fra3}]norm[{j,Fra3}]])*(CDelta[-Ret3,-Fra3][{-k,-Ret3},{-l,-Fra3}]norm[{l,Fra3}]PD[{0,-Ret}][ex]
																					- \[Epsilon] r[] CDelta[-Ret3,-Fra3][{-k,-Ret3},{-l,-Fra3}]norm[{l,Fra3}] acc[{m,Fra3}]PD[{-m,-Fra3}][ex])]}];];


CommutedtaudFrame={PD[{-k_,-Fra3}][PD[{0,-Ret}][tens_]]:>
					Module[{i,j,l,m},-\[Epsilon] r[] CDelta[-Fra3,-Fra3][{-k,-Fra3},{-j,-Fra3}] norm[{j,Fra3}] acc1d[{i,Fra3}]PD[{-i,-Fra3}][tens]
					-\[Epsilon](1/Scalar[1 + \[Epsilon] r[] acc[{-j,-Fra3}]norm[{j,Fra3}]])*(r[] acc1d[{-i,-Fra3}]norm[{i,Fra3}]CDelta[-Fra3,-Fra3][{-k,-Fra3},{-m,-Fra3}]norm[{m,Fra3}]PD[{0,-Ret}][tens]
														- \[Epsilon] r[]^2 acc1d[{-i,-Fra3}]norm[{i,Fra3}]CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}]norm[{l,Fra3}]acc[{m,Fra3}]PD[{-m,-Fra3}][tens])
					+PD[{0,-Ret}][PD[{-k,-Fra3}][tens]]]};


IntNull/:IntNull[PD[-{0,Ret}][expr2_]]:=PD[-{0,Fra}][IntNull[ expr2]];


IntNull[Basis[{a_,-bas1_},{b_,bas2_}]expr_]/;MatchQ[bas1,(Fra|Fra3)]&&MatchQ[bas2,(Fra|Fra3)]:=Basis[{a,-bas1},{b,bas2}]IntNull[expr];
IntNull[Basis[{b_,bas2_},{a_,-bas1_}]expr_]/;MatchQ[bas1,(Fra|Fra3)]&&MatchQ[bas2,(Fra|Fra3)]:=Basis[{b,bas2},{a,-bas1}]IntNull[expr];


(* ::Subsubsection:: *)
(*Angular Integration*)


CommuteThroughSNullInt={};


SIntExclusionpattern=PlaceholderNothing;


DefN[v_,M_?ManifoldQ,pa_]:=With[{tangent=TangentBundleOfManifold[M]},
xTensorQ[v]^:=True;
Dagger[v]^:=v;
DefInfo[v]^:={"tensor",""};
DependenciesOfTensor[v]^:={M};
HostsOf[v]^:={M,tangent};
SlotsOfTensor[v]^:={AnyIndices@tangent};
SymmetryGroupOfTensor[v[inds__]]/;Length[{inds}]>1^:=StrongGenSet[#,GenSet[Sequence@@(Cycles[{Range[Length[{inds}]][[#]],Range[Length[{inds}]][[#+1]]}]&/@Range[Length[{inds}]-1])]]&@Range@Length@{inds};
SymmetryGroupOfTensor[v[inds__]]/;Length[{inds}]===1^:=StrongGenSet[{},GenSet[]];
TensorID[v]^:={};
];


DefN[Ns,M4,"N"];


(* ::Text:: *)
(*I may well need the symmetric-trace-free version of this, but It's not yet clear to me how the rules for that should work in the null coordinates, so I'll omit it for now.*)


(* ::Text:: *)
(*Null norms.*)


Ns/:(Ns[___,a_,___,-a_,___])/;VBundleOfIndex[a]==TangentM4:=0;
Ns/:(Ns[___,-a_,___,a_,___])/;VBundleOfIndex[a]==TangentM4:=0;
Ns/:(Ns[___,{a_,Ret3},___,{-a_,-Ret3},___]):=0;
Ns/:(Ns[___,{-a_,-Ret3},___,{a_,Ret3},___]):=0;
Ns/:(Ns[first___,{a_,Fra3},middle___,{-a_,-Fra3},last___]):=Ns[first,middle,last];
Ns/:(Ns[first___,{-a_,-Fra3},middle___,{a_,Fra3},last___]):=Ns[first,middle,last];
Ns/:(Ns[first___,{0,Fra},last___]):=Ns[first,last];


Ns/:PD[a_][Ns[inds__]]:=Plus@@((PD[a][norm[{inds}[[#]]]] * Ns@@(Delete[{inds},#]) )& /@Range[Length[{inds}]]);
Ns[]:=1;


Tex[Ns]:="N"


ExplodeNrule:={Ns[indices___]:>Times@@(norm/@{indices})};


nstoNsrule={
norm[{i_,Fra3}]:>Ns[{i,Fra3}],
norm[{i_,Fra3}]norm[{j_,Fra3}]:>Ns[{i,Fra3},{j,Fra3}],
norm[{i_,Fra3}]Ns[indices___]:>Ns[{i,Fra3},indices],
Ns[indices1___]Ns[indices2___]:>Ns[indices1,indices2]};


Ns/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]Ns[first___,{a_,Fra3},mid___,{b_,Fra3},last___]:=Ns[first,mid,last];
Ns/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]Ns[first___,{b_,Fra3},mid___,{a_,Fra3},last___]:=Ns[first,mid,last];


CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]IntNull[Ns[first___,{a_,Fra3},mid___,{b_,Fra3},last___]]:=IntNull[Ns[first,mid,last]];
CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]IntNull[Ns[first___,{b_,Fra3},mid___,{a_,Fra3},last___]]:=IntNull[Ns[first,mid,last]];
CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]IntNull[Ns[first___,{a_,Fra3},mid___,{b_,Fra3},last___] exp_]:=IntNull[Ns[first,mid,last]*exp];
CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]IntNull[Ns[first___,{b_,Fra3},mid___,{a_,Fra3},last___] exp_]:=IntNull[Ns[first,mid,last]*exp];
CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]IntNull[Ns[first___,{a_,Fra3},mid___,{b_,Fra3},last___] exp_,expr___]:=IntNull[Ns[first,mid,last]exp,expr];
CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]IntNull[Ns[first___,{b_,Fra3},mid___,{a_,Fra3},last___] exp_,expr___]:=IntNull[Ns[first,mid,last]exp,expr];


CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]SIntNull[Ns[first___,{a_,Fra3},mid___,{b_,Fra3},last___]]:=SIntNull[Ns[first,mid,last]];
CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]SIntNull[Ns[first___,{b_,Fra3},mid___,{a_,Fra3},last___]]:=SIntNull[Ns[first,mid,last]];
CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]SIntNull[Ns[first___,{a_,Fra3},mid___,{b_,Fra3},last___] exp_]:=SIntNull[Ns[first,mid,last]*exp];
CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]SIntNull[Ns[first___,{b_,Fra3},mid___,{a_,Fra3},last___] exp_]:=SIntNull[Ns[first,mid,last]*exp];
CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]SIntNull[Ns[first___,{a_,Fra3},mid___,{b_,Fra3},last___] exp_,expr___]:=SIntNull[Ns[first,mid,last]exp,expr];
CDelta/:CDelta[-Fra3,-Fra3][{-a_,-Fra3},{-b_,-Fra3}]SIntNull[Ns[first___,{b_,Fra3},mid___,{a_,Fra3},last___] exp_,expr___]:=SIntNull[Ns[first,mid,last]exp,expr];


CDelta/:CDelta[Fra3,-Fra3][{i_,Fra3},{-k_,-Fra3}]IntNull[ex___,exp_*tens_[first___,{k_,Fra3},last___]]:=IntNull[ex,exp*tens[first,{i,Fra3},last]];
CDelta/:CDelta[Fra3,-Fra3][{i_,Fra3},{-k_,-Fra3}]IntNull[exp_*tens_[first___,{k_,Fra3},last___]]:=IntNull[exp*tens[first,{i,Fra3},last]];
CDelta/:CDelta[Fra3,-Fra3][{i_,Fra3},{-k_,-Fra3}]IntNull[tens_[first___,{k_,Fra3},last___]]:=IntNull[tens[first,{i,Fra3},last]];
CDelta/:CDelta[-Fra3,Fra3][{-k_,-Fra3},{i_,Fra3}]IntNull[ex___,exp_*tens_[first___,{k_,Fra3},last___]]:=IntNull[ex,exp*tens[first,{i,Fra3},last]];
CDelta/:CDelta[-Fra3,Fra3][{-k_,-Fra3},{i_,Fra3}]IntNull[exp_*tens_[first___,{k_,Fra3},last___]]:=IntNull[exp*tens[first,{i,Fra3},last]];
CDelta/:CDelta[-Fra3,Fra3][{-k_,-Fra3},{i_,Fra3}]IntNull[tens_[first___,{k_,Fra3},last___]]:=IntNull[tens[first,{i,Fra3},last]];
CDelta/:CDelta[Fra3,-Fra3][{i_,Fra3},{-k_,-Fra3}]SIntNull[ex___,exp_*tens_[first___,{k_,Fra3},last___]]:=SIntNull[ex,exp*tens[first,{i,Fra3},last]];
CDelta/:CDelta[Fra3,-Fra3][{i_,Fra3},{-k_,-Fra3}]SIntNull[exp_*tens_[first___,{k_,Fra3},last___]]:=SIntNull[exp*tens[first,{i,Fra3},last]];
CDelta/:CDelta[Fra3,-Fra3][{i_,Fra3},{-k_,-Fra3}]SIntNull[tens_[first___,{k_,Fra3},last___]]:=SIntNull[tens[first,{i,Fra3},last]];
CDelta/:CDelta[-Fra3,Fra3][{-k_,-Fra3},{i_,Fra3}]SIntNull[ex___,exp_*tens_[first___,{k_,Fra3},last___]]:=SIntNull[ex,exp*tens[first,{i,Fra3},last]];
CDelta/:CDelta[-Fra3,Fra3][{-k_,-Fra3},{i_,Fra3}]SIntNull[exp_*tens_[first___,{k_,Fra3},last___]]:=SIntNull[exp*tens[first,{i,Fra3},last]];
CDelta/:CDelta[-Fra3,Fra3][{-k_,-Fra3},{i_,Fra3}]SIntNull[tens_[first___,{k_,Fra3},last___]]:=SIntNull[tens[first,{i,Fra3},last]];


Unprotect[Basis];
Basis/:Basis[{i_,Fra3},{-k_,-Fra3}]IntNull[ex___,exp_*tens_[first___,{k_,Fra3},last___]]:=IntNull[ex,exp*tens[first,{i,Fra3},last]];
Basis/:Basis[{i_,Fra3},{-k_,-Fra3}]IntNull[exp_*tens_[first___,{k_,Fra3},last___]]:=IntNull[exp*tens[first,{i,Fra3},last]];
Basis/:Basis[{i_,Fra3},{-k_,-Fra3}]IntNull[tens_[first___,{k_,Fra3},last___]]:=IntNull[tens[first,{i,Fra3},last]];
Basis/:Basis[{i_,Fra3},{-k_,-Fra3}]SIntNull[ex___,exp_*tens_[first___,{k_,Fra3},last___]]:=SIntNull[ex,exp*tens[first,{i,Fra3},last]];
Basis/:Basis[{i_,Fra3},{-k_,-Fra3}]SIntNull[exp_*tens_[first___,{k_,Fra3},last___]]:=SIntNull[exp*tens[first,{i,Fra3},last]];
Basis/:Basis[{i_,Fra3},{-k_,-Fra3}]SIntNull[tens_[first___,{k_,Fra3},last___]]:=SIntNull[tens[first,{i,Fra3},last]];
Protect[Basis];


(* ::Text:: *)
(*automate this conversion - probably not too hazardous.*)


Ns/:Ns[indices1___]Ns[indices2___]:=Ns[indices1,indices2];


(*norm/:norm[{i_,Fra3}]:=Ns[{i,Fra3}];
Ns/:Ns[indices1___]Ns[indices2___]:=Ns[indices1,indices2];*)


(* ::Text:: *)
(*Source vanishes at surface*)


SIntNull/:SIntNull[expr_ CurrentDens[__]]:=0;
SIntNull/:SIntNull[expr_ CurrentDenspert[__]]:=0;
SIntNull/:SIntNull[CurrentDens[__]]:=0;
SIntNull/:SIntNull[CurrentDenspert[__]]:=0;


SIntNull/:HoldPattern[SIntNull[ex_[inds___]*exp_]/;MemberQ[CommuteThroughSNullInt,ex]]:=ex[inds]SIntNull[exp];
SIntNull/:HoldPattern[SIntNull[(ex_[inds___])^2*exp_]/;MemberQ[CommuteThroughSNullInt,ex]]:=(ex[inds])^2 SIntNull[exp];
SIntNull/:HoldPattern[SIntNull[PD[ind_][ex_[inds___]]*exp_]/;MemberQ[CommuteThroughSNullInt,ex]&&FreeQ[ind,(Ret|Ret3)]]:=PD[ind][ex[inds]]SIntNull[exp];
SIntNull/:HoldPattern[SIntNull[(PD[{0,-Fra}][ex_[inds___]])^2*exp_]/;MemberQ[CommuteThroughSNullInt,ex]]:=(PD[{0,-Fra}][ex[inds]])^2 SIntNull[exp];
SIntNull/:HoldPattern[SIntNull[PD[ind1_]@PD[ind2_][ex_[inds___]]*exp_]/;MemberQ[CommuteThroughSNullInt,ex]&&FreeQ[{ind1,ind2},(Ret|Ret3)]]:=PD[ind1]@PD[ind2][ex[inds]]SIntNull[exp];
SIntNull/:HoldPattern[SIntNull[PD[{0,-Fra}]@PD[{0,-Fra}]@PD[{0,-Fra}][ex_[inds___]]*exp_]/;MemberQ[CommuteThroughSNullInt,ex]]:=PD[{0,-Fra}]@PD[{0,-Fra}]@PD[{0,-Fra}][ex[inds]]SIntNull[exp];


SIntNull/:HoldPattern[SIntNull[ex1_*Scalar[ex2_]]]:=SIntNull[ex1*Scalar[ex2]//NoScalar];
SIntNull/:HoldPattern[SIntNull[ex1_*Scalar[ex2_]^2]]:=SIntNull[ex1*(Scalar[ex2]^2//NoScalar)];


SIntNull/:HoldPattern[SIntNull[r[]^pow_  Ns[inds__]]]/;OddQ[Length[{inds}]]:=0;
SIntNull/:HoldPattern[SIntNull[r[]^pow_  Ns[inds__]]]/;EvenQ[Length[{inds}]]&&And@@(UpIndexQ/@{inds}):=
									(Module[{l=Length[{inds}]},(4Pi/(l+1))R[]^(pow+2)Symmetrize[Times@@(CDelta[Fra3,Fra3]@@#&/@Partition[{inds},2]),{inds}]])//ExpandAll;
SIntNull/:HoldPattern[SIntNull[Ns[inds__]]]/;OddQ[Length[{inds}]]:=0;
SIntNull/:HoldPattern[SIntNull[Ns[inds__]]]/;EvenQ[Length[{inds}]]&&And@@(UpIndexQ/@{inds}):=
									Module[{l=Length[{inds}]},(4Pi/(l+1))(1/(1))R[]^(2)Symmetrize[Times@@(CDelta[Fra3,Fra3]@@#&/@Partition[{inds},2]),{inds}]];
SIntNull/:HoldPattern[SIntNull[r[]^pow_]]:=(4Pi)R[]^(pow+2);


SIntExclusion=(CurrentDens | CurrentDenspert);


SIntNullRules={
HoldPattern[SIntNull[r[]^pow_ expr_ Ns[inds__]]]/;FreeQ[expr,(Ns|r)]&&FreeQ[expr,SIntExclusion]&&OddQ[Length[{inds}]]:>0,
HoldPattern[SIntNull[r[]^pow_ expr_ Ns[inds__]]]/;FreeQ[expr,(Ns|r)]&&FreeQ[expr,SIntExclusion]&&EvenQ[Length[{inds}]]&&And@@(UpIndexQ/@{inds}):>
									Module[{l=Length[{inds}]},expr(4Pi/(l+1))R[]^(pow+2) Symmetrize[Times@@(CDelta[Fra3,Fra3]@@#&/@Partition[{inds},2]),{inds}]],
HoldPattern[SIntNull[expr_ Ns[inds__]]]/;FreeQ[expr,(Ns|r)]&&FreeQ[expr,SIntExclusion]&&OddQ[Length[{inds}]]:>0,
HoldPattern[SIntNull[expr_ Ns[inds__]]]/;FreeQ[expr,(Ns|r)]&&FreeQ[expr,SIntExclusion]&&EvenQ[Length[{inds}]]&&And@@(UpIndexQ/@{inds}):>
									Module[{l=Length[{inds}]},expr(4Pi/(l+1))R[]^2 Symmetrize[Times@@(CDelta[Fra3,Fra3]@@#&/@Partition[{inds},2]),{inds}]],
HoldPattern[SIntNull[r[]^pow_  Ns[inds__]]]/;OddQ[Length[{inds}]]:>0,
HoldPattern[SIntNull[r[]^pow_  Ns[inds__]]]/;EvenQ[Length[{inds}]]&&And@@(UpIndexQ/@{inds}):>
									Module[{l=Length[{inds}]},(4Pi/(l+1))R[]^(pow+2)Symmetrize[Times@@(CDelta[Fra3,Fra3]@@#&/@Partition[{inds},2]),{inds}]],
HoldPattern[SIntNull[r[]^pow_ expr_]]/;FreeQ[expr,(Ns|r)]&&FreeQ[expr,SIntExclusion]:>expr(4Pi)R[]^(pow+2),
HoldPattern[SIntNull[r[]^pow_]]:>(4Pi)R[]^(pow+2),
HoldPattern[SIntNull[expr_ ]]/;FreeQ[expr,(Ns|r)]&&FreeQ[expr,SIntExclusion]:>expr(4Pi)R[]^2,
HoldPattern[SIntNull[Ns[inds__]]]/;OddQ[Length[{inds}]]:>0,
HoldPattern[SIntNull[Ns[inds__]]]/;EvenQ[Length[{inds}]]&&And@@(UpIndexQ/@{inds}):>
									Module[{l=Length[{inds}]},(4Pi/(l+1))(1/(1))R[]^(2)Symmetrize[Times@@(CDelta[Fra3,Fra3]@@#&/@Partition[{inds},2]),{inds}]]};


NullIntRules=SIntNullRules~Join~NullIntparts~Join~nstoNsrule;
