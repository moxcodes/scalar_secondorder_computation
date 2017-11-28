(* ::Package:: *)

(* ::Subsection:: *)
(*Tensor definitions*)


(* ::Text:: *)
(*xTensor definition calls for stress energy T^(\[Mu]\[Vee]), \[Rho]*)


DefTensor[SE[a,b],{M4},Symmetric[{a,b}],PrintAs->"T"];
DefTensorPerturbation[SEpert[LI[o],a,b],SE[a,b],{M4},Symmetric[{a,b}],PrintAs->"T"];
DefTensor[SourceDens[],{M4},PrintAs->"\[Rho]"];
DefTensorPerturbation[SourceDenspert[LI[o]],SourceDens[],{M4},PrintAs->"\[Rho]"];


(* ::Text:: *)
(*xTensor definitions for the field strength tensor - it will be more convenient to have it as a separate object*)


DefTensor[Phfieldr[],{M4},PrintAs->"\!\(\*SubscriptBox[\(\[CapitalPhi]\), \(-\)]\)"];


DefTensor[Phstr[a],{M4},PrintAs->"\[Del]\[CapitalPhi]"];
DefTensorPerturbation[Phstrpert[LI[ord],a],Phstr[a],{M4},PrintAs->"\[Del]\[CapitalPhi]"];


DefTensor[PhstrExt[a],{M4},PrintAs->"\[Del]\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \((ext)\)]\)"];


DefTensor[Charge[],{M4},PrintAs->"q"];


DefTensorPerturbation[Chargepert[LI[o]],Charge[],{M4},PrintAs->"q"];


DefTensor[ChargeDipole[a],{M4},PrintAs->"Q"];


DefTensorPerturbation[ChargeDipolepert[LI[o],a],ChargeDipole[a],{M4},PrintAs->"Q"];


(* ::Text:: *)
(*Renormalized tensors:*)


WLTensors={acc,accpert,acc1d,acc1dpert};


WLTensors=WLTensors~Join~{Charge,Chargepert,ChargeDipole,ChargeDipolepert};


(* ::Text:: *)
(*For retarded coordinates, it's necessary to deal with worldline quantities off the worldline, as (for instance), the acceleration frame components appear in the basis vectors.*)
(*When expressing these quantities in terms of Frame-projected derivatives, we can take advantage of the constraint that \!\( *)
(*\*SubscriptBox[\(\[PartialD]\), \(i\)]*)
(*\*SuperscriptBox[\(T\), \( *)
(*\*OverscriptBox[\(k\), \(^\)] ... \)]\) = 0. This is effectively parallel transport - contraction with the frame vectors*)


WLFrame3PDConvert[expr_]:=Module[{PDTempForm=expr//.toPDTemp},

Return[((PDTempForm//.{PDTemp[pre__,{i_,-Fra3},post___][tens_[tensinds__]]/;MemberQ[WLTensors,tens]&&(And@@(MemberQ[{Fra,Fra3,-Fra,-Fra3},#[[2]]]&/@{tensinds})):>
						Module[{j},PDTemp[pre][-CDelta[-Fra3,-Ret3][{i,-Fra3},{-j,-Ret3}]norm[{j,Ret3}]]PDTemp[{0,-Fra},post][tens[tensinds]]
									-CDelta[-Fra3,-Ret3][{i,-Fra3},{-j,-Ret3}]norm[{j,Ret3}]PDTemp[pre,{0,-Fra},post][tens[tensinds]]],
						PDTemp[{i_,-Fra3},post___][tens_[tensinds__]]/;MemberQ[WLTensors,tens]&&(And@@(MemberQ[{Fra,Fra3,-Fra,-Fra3},#[[2]]]&/@{tensinds})):>
						Module[{j},-CDelta[-Fra3,-Ret3][{i,-Fra3},{-j,-Ret3}]norm[{j,Ret3}]PDTemp[{0,-Fra},post][tens[tensinds]]]})//.fromPDTemp)//Expand];
];


Unprotect[PD];


DefConstantSymbol[\[Lambda]];


PD/:PD[{-i_,-Ret3}][tens_[inds__]]/;MemberQ[WLTensors,tens]&&(And@@(MemberQ[{Fra,Fra3,-Fra,-Fra3},#[[2]]]&/@{inds})):=0;


(* ::Subsubsection:: *)
(*Tensor documentation*)


SE::usage="SE is the symbol \!\(\*SubscriptBox[\(T\), \(\[Upsilon]\[Nu]\)]\) in the accompanying paper - it represents 
the sum of the retarded field contribution and the matter contribution - it is two-index and symmetric";
SEpert::usage"SEpert is the perturbed form of SE. The zeroth order is simply SE. Two index and symmetric.";


SourceDens::usage="SourceDens is the symbol \!\(\*SubscriptBox[\(\[Rho]\), \(\[Upsilon]\)]\) from the accompanying paper 
it represents the charge-current vector, explicitly with compact support on the worldtube. one-index object.";
SourceDenspert::usage"SourceDenspert is the perturbed form of SourceDens. one-index object.";


Phfieldr::usage="Phfieldr is the retarded vector 4-potential for the electromagnetic field. one-index object.
Replacement rules : PhfieldRules and ScaledPhfieldRules";


PhstrExt::usage="PhstrExt is the external (forcing) field strength. We choose to not expand its possible \[Epsilon] dependence.";


Phstr::usage="Phstr is the field-strength tensor from the retarded self-field Phfieldr. It is an antisymmetric two-index object.
Replacement rules: PhstrfieldRules.";


Phstrpert::usage="Phstrpert is the perturbed form of the field-strength Fstr. It is an antisymmetric two-index object.
The replacement rules assume a simultaneous expansion in \[Epsilon]^n and 1/r^m, and are written as Phstrpert[LI[{n,m}],a,b].
The set of replacement rules: Phstrfieldrulespert";


(* ::Subsection:: *)
(*Perturbation rules and overrides*)


(* ::Subsubsection:: *)
(*Perturbation rules*)


Unprotect[Perturbation];
Perturbation/:Perturbation[PhstrExt[inds___],0]:=PhstrExt[inds];
Perturbation/:Perturbation[PhstrExt[inds___]]:=Module[{i},r[]Ns[{i,Fra3}]CD[-{i,Fra3}][PhstrExt[inds]] + r[]CD[-{0,Fra}][PhstrExt[inds]]];
Perturbation/:Perturbation[PhstrExt[inds___],1]:=Module[{i},r[]Ns[{i,Fra3}]CD[-{i,Fra3}][PhstrExt[inds]] + r[]CD[-{0,Fra}][PhstrExt[inds]]];
Perturbation/:Perturbation[PhstrExt[inds___],2]:=Module[{i,j},r[]^2 Ns[{i,Fra3},{j,Fra3}]CD[-{i,Fra3}][CD[-{j,Fra3}][PhstrExt[inds]]] + 2 r[]^2 Ns[{i,Fra3}]CD[-{i,Fra3}][CD[-{0,Fra}][PhstrExt[inds]]]
																+ r[]^2 CD[-{0,Fra}][CD[-{0,Fra}][PhstrExt[inds]]]]
Perturbation/:Perturbation[PhstrExt[inds___],n_]:=Module[{indices=(Unique[a]&/@Range[n]),TempExpr=PhstrExt[inds]},
										For[ii=1,ii<=n,ii=ii+1,
											TempExpr=CD[-indices[[ii]]][TempExpr];];
										Return[Ns[Sequence@@indices]r[]^n TempExpr//Frame31Split]];
Protect[Perturbation];


PhstrExt/:PhstrExt[{-0,-Fra}]:=-PhstrExt[{0,Fra}];
PhstrExt/:PhstrExt[{-i_,-Fra3}]:=Module[{j},CDelta[-Fra3,-Fra3][-{i,Fra3},-{j,Fra3}]PhstrExt[{j,Fra3}]];


\[Epsilon]/:Perturbation[\[Epsilon],i_]/;i>=1:=0;
\[Epsilon]/:Perturbation[\[Epsilon],0]:=\[Epsilon];
\[Epsilon]/:Perturbation[\[Epsilon]]:=0;


norm/:Perturbation[norm[u_][{ind_,Ret3|Fra3|-Fra3}]]:=0;
norm/:Perturbation[norm[u_][{ind_,Ret3|Fra3|-Fra3}],i_]/;i>=1:=0;


Ns/:Perturbation[Ns[__]]:=0;
Ns/:Perturbation[Ns[__],i_]/;i>=1:=0;


r/:Perturbation[r[],i_]/;i>=1:=0;
r/:Perturbation[r[],0]:=r[];
r/:Perturbation[r[]]:=0;


CDelta/:Perturbation[CDelta[rank__][inds__],i_]/;DeltaValid[CDelta[rank][inds]]&&i>=1:=0;
CDelta/:Perturbation[CDelta[rank__][inds__],0]/;DeltaValid[CDelta[rank][inds]]:=CDelta[rank][inds];
CDelta/:Perturbation[CDelta[rank__][inds__]]/;DeltaValid[CDelta[rank][inds]]:=0;


(* ::Text:: *)
(*Just because the acceleration vector is purely spatial, and the frame indices are orthonormal.*)


acc/:Perturbation[acc[{ind_,-Fra3}]]:=accpert[LI[1],{ind,-Fra3}];
acc/:Perturbation[acc[{ind_,-Fra3}],num_]:=accpert[LI[num],{ind,-Fra3}];


(* ::Subsubsection:: *)
(*Custom perturbation code*)


(* ::Text:: *)
(*I have found that the xtensor perturbation function drags a bit.  I've defined a thin version as an optimization step*)


(* ::Text:: *)
(*TODO:re-write most of these rules to be more consise (a list of objects and perturbations, loop through and generate the 4 rules each pair needs)*)


(* ::Text:: *)
(*This assumes we never reduce order :*)


P[expr_Plus]:=P/@expr;
P[expr_Times]:=Plus@@(((P[expr[[#]]]*Times@@(Delete[List@@expr,#]))&)/@Range[Length[expr]]);
P[expr_^n_]:=n*P[expr]*expr^(n-1);
P[Charge[]]           :=Chargepert[LI[1]];
P[Chargepert[LI[o_]]]:=Chargepert[LI[o+1]];
P[ChargeDipole[inds__]]           :=ChargeDipolepert[LI[1],inds];
P[ChargeDipolepert[LI[o_],inds__]]:=ChargeDipolepert[LI[o+1],inds];
P[ChargeQuadPole[inds__]]           :=ChargeQuadPole[LI[1],inds];
P[ChargeQuadPolepert[LI[o_],inds__]]:=ChargeQuadPolepert[LI[o+1],inds];
P[RCharge[]]            :=RChargepert[LI[1]];
P[RChargepert[LI[o_]]] :=RChargepert[LI[o+1]];
P[RChargeDipole[inds__]]           :=RChargeDipolepert[LI[1],inds];
P[RChargeDipolepert[LI[o_],inds__]]:=RChargeDipolepert[LI[o+1],inds];
P[RChargeQuadPole[inds__]]           :=RChargeQuadPole[LI[1],inds];
P[RChargeQuadPolepert[LI[o_],inds__]]:=RChargeQuadPolepert[LI[o+1],inds];
P[Phstr[inds__]]:=Phstrpert[LI[1],inds];
P[Phstrpert[LI[o_],inds__]]:=Phstrpert[LI[o+1],inds];
P[acc[ind_]]             :=0;
P[accpert[LI[o_],ind_]]  :=0;
P[acc1d[ind_]]           :=0;
P[acc1dpert[LI[o_],ind_]]:=0;
P[norm[__]]:=0;
P[r[]]:=0;
P[r[]]:=0;
P[\[Epsilon]]:=0;
P[expr_?NumericQ]:=0;
P[CDelta[__][__]]:=0;
P[PD[-{0,Ret}][expr_]]:=PD[-{0,Ret}][P[expr]];
P[PD[junk__][expr_]]:=PD[junk][P[expr]];
P[\[Lambda]]:=0;
P[PD[arg_][expr_]]:=PD[arg][P[expr]];
P[PD[arg_][expr_],n_]:=PD[arg][P[expr,n]];
P[SE[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=SEpert[LI[1],inds];
P[SE[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=SEpert[LI[n],inds];
P[SEpert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=SEpert[LI[o+1],inds];
P[SEpert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=SEpert[LI[o+n],inds];
P[SourceDens[]]:=SourceDenspert[LI[1]];
P[SourceDens[],n_]:=SourceDenspert[LI[n]];
P[SourceDenspert[LI[o_]]]:=SourceDenspert[LI[o+1]];
P[SourceDenspert[LI[o_]],n_]:=SourceDenspert[LI[o+n]];
P[Mom[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=Mompert[LI[1],inds];
P[Mom[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=Mompert[LI[n],inds];
P[Mompert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=Mompert[LI[o+1],inds];
P[Mompert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=Mompert[LI[o+n],inds];
P[HMom[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=HMompert[LI[1],inds];
P[HMom[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=HMompert[LI[n],inds];
P[HMompert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=HMompert[LI[o+1],inds];
P[HMompert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=HMompert[LI[o+n],inds];
P[Spin[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=Spinpert[LI[1],inds];
P[Spin[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=Spinpert[LI[n],inds];
P[Spinpert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=Spinpert[LI[o+1],inds];
P[Spinpert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=Spinpert[LI[o+n],inds];
P[HSpin[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=HSpinpert[LI[1],inds];
P[HSpin[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=HSpinpert[LI[n],inds];
P[HSpinpert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=HSpinpert[LI[o+1],inds];
P[HSpinpert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=HSpinpert[LI[o+n],inds];
P[Ns[inds__]]:=0;
P[Scalar[expr_]]:=P[GenerateNewDummies[expr]];


P[IntNull[expr_]]:=IntNull[P[expr]];


P[CD[inds_][tens_]]:=CD[inds][P[tens]];
Q[CD[inds_][tens_]]:=CD[inds][Q[tens]];
Q[SourceDens[__]]:=0;Q[SourceDenspert[__]]:=0;


ApplyPtoPhstrExt={P[P[PhstrExt[inds__]]]/;FreeQ[{inds},(Ret|Ret3)]:>Perturbation[PhstrExt[inds],2],
			  P[PhstrExt[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:>Perturbation[PhstrExt[inds]]};


Perturb[expr_,n_]:=Plus@@((((\[Epsilon]^#/#!)Nest[P,expr,#])&)/@Range[0,n]);


(* ::Subsection:: *)
(*Body parameter index*)


(* ::Text:: *)
(*Removed legacy code from here, may need to replace if things break*)


DefTensor[Mom[a],{M4},PrintAs->"P"];
DefTensorPerturbation[Mompert[LI[order],a],Mom[a],{M4},PrintAs->"P"];


DefTensor[HMom[a],{M4},PrintAs->"\!\(\*OverscriptBox[\(P\), \(~\)]\)"];
DefTensorPerturbation[HMompert[LI[o],a],HMom[a],{M4},PrintAs->"\!\(\*OverscriptBox[\(P\), \(~\)]\)"];


DefTensor[Spin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"S"];
DefTensorPerturbation[Spinpert[LI[o],a,b],Spin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"S"];


DefTensor[HSpin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*OverscriptBox[\(S\), \(~\)]\)"];
DefTensorPerturbation[HSpinpert[LI[o],a,b],HSpin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*OverscriptBox[\(S\), \(~\)]\)"];


DefTensor[ChargeQuadPole[a,b],{M4},Symmetric[{a,b}],PrintAs->"Q"];
DefTensorPerturbation[ChargeQuadPolepert[LI[o],a,b],ChargeQuadPole[a,b],{M4},Symmetric[{a,b}],PrintAs->"Q"];


$BodyParams={Mom,Mompert,
			 Spin,Spinpert,
             Charge,Chargepert,
			 ChargeDipole,ChargeDipolepert,
			 ChargeQuadPole,ChargeQuadPolepert};


Unprotect[PD];
PD[{-i_,-Ret3}][tens_[inds___]]/;MemberQ[$BodyParams,tens]&&FreeQ[inds,(Ret|Ret3)]:=0;
PD[{-i_,-Ret3}][PD[__][tens_[inds___]]]/;MemberQ[$BodyParams,tens]&&FreeQ[inds,(Ret|Ret3)]:=0;
PD[{-i_,-Ret3}][PD[__][PD[__][tens_[inds___]]]]/;MemberQ[$BodyParams,tens]&&FreeQ[inds,(Ret|Ret3)]:=0;
Protect[PD];


ConvertScalediFraDerivs={PD[{-i_,-Fra3}][tens_[inds___]]/;MemberQ[$BodyParams,tens]&&FreeQ[{inds},(Ret|Ret3)]:>-\[Epsilon] norm[{-i,-Fra3}]PD[{0,-Fra}][tens[inds]],
PD[{-i_,-Fra3}][PD[pdind__][tens_[inds___]]]/;MemberQ[$BodyParams,tens]&&FreeQ[{inds},(Ret|Ret3)]:>-\[Epsilon] norm[{-i,-Fra3}]PD[{0,-Fra}][PD[pdind][tens[inds]]],
PD[{-i_,-Fra3}][PD[pdind1__][PD[pdind2__][tens_[inds___]]]]/;MemberQ[$BodyParams,tens]&&FreeQ[{inds},(Ret|Ret3)]
				:>-\[Epsilon] norm[{-i,-Fra3}]PD[{0,-Fra}][PD[pdind1][PD[pdind2][tens[inds]]]],
PD[{-i_,-Fra3}][PD[pdind1__][PD[pdind2__][PD[pdind3_][tens_[inds___]]]]]/;MemberQ[$BodyParams,tens]&&FreeQ[{inds},(Ret|Ret3)]
				:>-\[Epsilon] norm[{-i,-Fra3}]PD[{0,-Fra}][PD[pdind1][PD[pdind2][PD[pdind3][tens[inds]]]]]};


MomentumSumRuleList=
Module[{partialList={},ii,jj},
	For[jj=0,jj<=3,jj++,
		partialList=partialList~Join~
				{{{Nest[PD[{0,-Fra}],IntNull[(SE[{0,Fra},{i,Fra3}]|SE[{i,Fra3},{0,Fra}])],jj],
		-Nest[PD[{0,-Fra}],IntNull[(SE[{k_,Fra3},{i,Fra3}] | SE[{i,Fra3},{k_,Fra3}])Ns[{l_,Fra3}]],jj]
			 (CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-l_,-Fra3}]|CDelta[-Fra3,-Fra3][{-l_,-Fra3},{-k_,-Fra3}])},
			{{i_},{i}},Nest[PD[{0,-Fra}],Mom[{i,Fra3}],jj]},
				{{Nest[PD[{0,-Fra}],IntNull[(SE[{0,Fra},{0,Fra}]|SE[{0,Fra},{0,Fra}])],jj],
		-Nest[PD[{0,-Fra}],IntNull[(SE[{k_,Fra3},{0,Fra}] | SE[{0,Fra},{k_,Fra3}])Ns[{l_,Fra3}]],jj]
			 (CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-l_,-Fra3}]|CDelta[-Fra3,-Fra3][{-l_,-Fra3},{-k_,-Fra3}])},
			{{},{}},Nest[PD[{0,-Fra}],Mom[{0,Fra}],jj]}};
		];

	For[ii=1,ii<=3,ii++,
		For[jj=ii,jj<=3,jj++,
		partialList=partialList~Join~
				{{{Nest[PD[{0,-Fra}],IntNull[(SEpert[LI[ii],{0,Fra},{i,Fra3}]|SEpert[LI[ii],{i,Fra3},{0,Fra}])],jj-ii],
		-Nest[PD[{0,-Fra}],IntNull[(SEpert[LI[ii],{k_,Fra3},{i,Fra3}] | SEpert[LI[ii],{i,Fra3},{k_,Fra3}])Ns[{l_,Fra3}]],jj-ii]
			 (CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-l_,-Fra3}]|CDelta[-Fra3,-Fra3][{-l_,-Fra3},{-k_,-Fra3}])},
			{{i_},{i}},Nest[PD[{0,-Fra}],Mompert[LI[ii],{i,Fra3}],jj-ii]},
				{{Nest[PD[{0,-Fra}],IntNull[(SEpert[LI[ii],{0,Fra},{0,Fra}]|SEpert[LI[ii],{0,Fra},{0,Fra}])],jj-ii],
		-Nest[PD[{0,-Fra}],IntNull[(SEpert[LI[ii],{k_,Fra3},{0,Fra}] | SEpert[LI[ii],{0,Fra},{k_,Fra3}])Ns[{l_,Fra3}]],jj-ii]
			 (CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-l_,-Fra3}]|CDelta[-Fra3,-Fra3][{-l_,-Fra3},{-k_,-Fra3}])},
			{{},{}},Nest[PD[{0,-Fra}],Mompert[LI[ii],{0,Fra}],jj-ii]}};
		];
		];
	Return[partialList];];


SpinSumRuleList=
Module[{partialList={},ii,jj},
	For[jj=0,jj<=2,jj++,
		partialList=partialList~Join~{{{Nest[PD[{0,-Fra}],IntNull[Ns[{i, Fra3}]*r[]*SE[{0, Fra}, {0, Fra}]],jj],
			 	-Nest[PD[{0,-Fra}],IntNull[r[]*(SE[{0, Fra}, {i, Fra3}]|SE[{i, Fra3}, {0, Fra}])],jj],
			    -(Nest[PD[{0,-Fra}],IntNull[(Ns[{i, Fra3}, {k_, Fra3}]|Ns[{k_, Fra3},{i, Fra3}])*r[]*(SE[{j_, Fra3}, {0, Fra}]|SE[{0, Fra}, {j_, Fra3}])],jj]
							*(CDelta[-Fra3, -Fra3][{-j_, -Fra3}, {-k_, -Fra3}] | CDelta[-Fra3, -Fra3][{-k_, -Fra3},{-j_, -Fra3}])),
				 Nest[PD[{0,-Fra}], IntNull[Ns[{j_, Fra3}]*r[]*(SE[{k_, Fra3}, {i, Fra3}]|SE[{i, Fra3}, {k_, Fra3}])],jj]
							*(CDelta[-Fra3, -Fra3][{-j_, -Fra3}, {-k_, -Fra3}]|CDelta[-Fra3, -Fra3][{-k_, -Fra3},{-j_, -Fra3}])},
					{{i_},{i}},Nest[PD[{0,-Fra}],Spin[{0,Fra},{i,Fra3}],jj]}
					,
				{{-Nest[PD[{0,-Fra}],IntNull[Ns[{k, Fra3}]*r[]*(SE[{0, Fra}, {j, Fra3}] |SE[{j, Fra3}, {0, Fra}] )],jj],
			 	Nest[PD[{0,-Fra}],IntNull[Ns[{j, Fra3}]*r[]*(SE[{0, Fra}, {k, Fra3}] |SE[{k, Fra3}, {0, Fra}] )],jj],
			   Nest[PD[{0,-Fra}], IntNull[(Ns[{k, Fra3}, {l_, Fra3}]|Ns[{l_, Fra3},{k, Fra3}])*r[]*(SE[ {i_, Fra3}, {j, Fra3}]|SE[{j, Fra3}, {i_, Fra3}] )],jj]
							*(CDelta[-Fra3, -Fra3][{-i_, -Fra3}, {-l_, -Fra3}]|CDelta[-Fra3, -Fra3][{-l_, -Fra3},{-i_, -Fra3}]),
				-Nest[PD[{0,-Fra}],IntNull[(Ns[{j, Fra3}, {l_, Fra3}]|Ns[{l_, Fra3},{j, Fra3} ])*r[]*(SE[{i_, Fra3}, {k, Fra3}] |SE[{k, Fra3}, {i_, Fra3}] )],jj]
							*(CDelta[-Fra3, -Fra3][{-i_, -Fra3}, {-l_, -Fra3}]|CDelta[-Fra3, -Fra3][{-l_, -Fra3},{-i_, -Fra3}])},
				  {{j_,k_},{j,k}},Nest[PD[{0,-Fra}],Spin[{k,Fra3},{j,Fra3}],jj]}

				};
	];
	For[ii=1,ii<=2,ii++,
		For[jj=ii,jj<=2,jj++,
			partialList=partialList~Join~
					{{{Nest[PD[{0,-Fra}],IntNull[Ns[{i, Fra3}]*r[]*SEpert[LI[ii], {0, Fra}, {0, Fra}]],jj-ii],
			 	-Nest[PD[{0,-Fra}],IntNull[r[]*(SEpert[LI[ii], {0, Fra}, {i, Fra3}]|SEpert[LI[ii], {i, Fra3}, {0, Fra}])],jj-ii],
			    -(Nest[PD[{0,-Fra}],IntNull[(Ns[{i, Fra3}, {k_, Fra3}]|Ns[{k_, Fra3},{i, Fra3}])*r[]*(SEpert[LI[ii], {j_, Fra3}, {0, Fra}]|SEpert[LI[ii], {0, Fra}, {j_, Fra3}])],jj-ii]
							*(CDelta[-Fra3, -Fra3][{-j_, -Fra3}, {-k_, -Fra3}] | CDelta[-Fra3, -Fra3][{-k_, -Fra3},{-j_, -Fra3}])),
				  Nest[PD[{0,-Fra}],IntNull[Ns[{j_, Fra3}]*r[]*(SEpert[LI[ii], {k_, Fra3}, {i, Fra3}]|SEpert[LI[ii], {i, Fra3}, {k_, Fra3}])],jj-ii]
							*(CDelta[-Fra3, -Fra3][{-j_, -Fra3}, {-k_, -Fra3}]|CDelta[-Fra3, -Fra3][{-k_, -Fra3},{-j_, -Fra3}])},
					{{i_},{i}},Nest[PD[{0,-Fra}],Spinpert[LI[ii],{0,Fra},{i,Fra3}],jj-ii]}
					,
					{{-Nest[PD[{0,-Fra}],IntNull[Ns[{k, Fra3}]*r[]*(SEpert[LI[ii], {0, Fra}, {j, Fra3}] |SEpert[LI[ii], {j, Fra3}, {0, Fra}] )],jj-ii],
			 	Nest[PD[{0,-Fra}],IntNull[Ns[{j, Fra3}]*r[]*(SEpert[LI[ii], {0, Fra}, {k, Fra3}] |SEpert[LI[ii], {k, Fra3}, {0, Fra}] )],jj-ii],
			    Nest[PD[{0,-Fra}],IntNull[(Ns[{k, Fra3}, {l_, Fra3}]|Ns[{l_, Fra3},{k, Fra3}])*r[]*(SEpert[LI[ii], {i_, Fra3}, {j, Fra3}]|SEpert[LI[ii], {j, Fra3}, {i_, Fra3}] )],jj-ii]
							*(CDelta[-Fra3, -Fra3][{-i_, -Fra3}, {-l_, -Fra3}]|CDelta[-Fra3, -Fra3][{-l_, -Fra3},{-i_, -Fra3}]),
				-Nest[PD[{0,-Fra}],IntNull[(Ns[{j, Fra3}, {l_, Fra3}]|Ns[{l_, Fra3},{j, Fra3} ])*r[]*(SEpert[LI[ii], {i_, Fra3}, {k, Fra3}] |SEpert[LI[ii], {k, Fra3}, {i_, Fra3}] )],jj-ii]
							*(CDelta[-Fra3, -Fra3][{-i_, -Fra3}, {-l_, -Fra3}]|CDelta[-Fra3, -Fra3][{-l_, -Fra3},{-i_, -Fra3}])},
				  {{j_,k_},{j,k}},Nest[PD[{0,-Fra}],Spinpert[LI[ii],{k,Fra3},{j,Fra3}],jj-ii]}};
			];
		];
	Return[partialList];
];


SpinMomSumRuleList=SpinSumRuleList~Join~MomentumSumRuleList;


(* ::Text:: *)
(*Omitted spin-squared rule. I hope it does not turn out that I badly needed it*)


ChargeMultipoleRules={
IntNull[SourceDens[]]:>Charge[],
IntNull[SourceDenspert[LI[o_]]]:>Chargepert[LI[o]]
,
IntNull[SourceDens[] r[] Ns[{i_,Fra3}]]:>Module[{k},ChargeDipole[{i,Fra3}]],
IntNull[SourceDens[]r[]]:>ChargeDipole[{0,Fra}],
IntNull[SourceDenspert[LI[o_]] r[] Ns[{i_,Fra3}]]:>Module[{k},ChargeDipolepert[LI[o],{i,Fra3}]],
IntNull[SourceDenspert[LI[o_]]r[]]:>ChargeDipolepert[LI[o],{0,Fra}]
,
IntNull[SourceDens[]r[]^2]:>ChargeQuadPole[{0,Fra},{0,Fra}],
IntNull[SourceDens[]r[]^2 Ns[{i_,Fra3}]]:>ChargeQuadPole[{0,Fra},{i,Fra3}],
IntNull[SourceDens[]r[]^2 Ns[{i_,Fra3},{j_,Fra3}]]:>ChargeQuadPole[{i,Fra3},{j,Fra3}],
IntNull[SourceDenspert[LI[o_]]r[]^2]:>ChargeQuadPolepert[LI[o],{0,Fra},{0,Fra}],
IntNull[SourceDenspert[LI[o_]]r[]^2 Ns[{i_,Fra3}]]:>ChargeQuadPolepert[LI[o],{0,Fra},{i,Fra3}],
IntNull[SourceDenspert[LI[o_]]r[]^2 Ns[{i_,Fra3},{j_,Fra3}]]:>ChargeQuadPolepert[LI[o],{i,Fra3},{j,Fra3}]
};


ApplyAllBodyParams[expr_]:=(expr/.ChargeMultipoleRules)//ApplySumRuleList[SpinMomSumRuleList];


RevBodyParamSubRule:={
Mompert[LI[o_],{a_,basa_}]/;MemberQ[{Fra3,Fra},basa]:>Module[{j,i},IntNull[SEpert[LI[o],{0,Fra},{a,basa}]]
								-IntNull[SEpert[LI[o],{j,Fra3},{a,basa}]Ns[{i,Fra3}]]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}] ],
Mom[{a_,basa_}]/;MemberQ[{Fra,Fra3},basa]:>Module[{j,i},IntNull[SE[{0,Fra},{a,basa}]]
								-IntNull[SE[{j,Fra3},{a,basa}]Ns[{i,Fra3}]]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}] ]
,
Spinpert[LI[o_],{0,Fra},{i_,Fra3}]:>Module[{k,j},-IntNull[SEpert[LI[o],{0,Fra},{i,Fra3}]r[]]+ IntNull[Ns[{i,Fra3}]r[] SEpert[LI[o],{0,Fra},{0,Fra}]]
						- IntNull[Ns[{i,Fra3},{k,Fra3}] SEpert[LI[o],{j,Fra3},{0,Fra}]r[]]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]
						+ IntNull[Ns[{j,Fra3}]SEpert[LI[o],{k,Fra3},{i,Fra3}]r[]] CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]],
Spinpert[LI[o_],{i_,Fra3},{0,Fra}]:>Module[{k,j},IntNull[SEpert[LI[o],{0,Fra},{i,Fra3}]r[]]- IntNull[Ns[{i,Fra3}]r[] SEpert[LI[o],{0,Fra},{0,Fra}]]
						+ IntNull[Ns[{i,Fra3},{k,Fra3}] SEpert[LI[o],{j,Fra3},{0,Fra}]r[]]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]
						- IntNull[Ns[{j,Fra3}]SEpert[LI[o],{k,Fra3},{i,Fra3}]r[]] CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]],
Spin[{0,Fra},{i_,Fra3}]:>Module[{k,j},-IntNull[SE[{0,Fra},{i,Fra3}]r[]]+ IntNull[Ns[{i,Fra3}]r[] SE[{0,Fra},{0,Fra}]]
						- IntNull[Ns[{i,Fra3},{k,Fra3}] SE[{j,Fra3},{0,Fra}]r[]]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]
						+ IntNull[Ns[{j,Fra3}]SE[{k,Fra3},{i,Fra3}]r[]] CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]],
Spin[{i_,Fra3},{0,Fra}]:>Module[{k,j},IntNull[SE[{0,Fra},{i,Fra3}]r[]]- IntNull[Ns[{i,Fra3}]r[] SE[{0,Fra},{0,Fra}]]
						+ IntNull[Ns[{i,Fra3},{k,Fra3}] SE[{j,Fra3},{0,Fra}]r[]]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]
						- IntNull[Ns[{j,Fra3}]SE[{k,Fra3},{i,Fra3}]r[]] CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]],
Spinpert[LI[o_],{j_,Fra3},{k_,Fra3}]:>Module[{i,l},-IntNull[SEpert[LI[o],{0,Fra},{j,Fra3}] Ns[{k,Fra3}]r[]] + IntNull[SEpert[LI[o],{0,Fra},{k,Fra3}]Ns[{j,Fra3}]r[]]
											+CDelta[-Fra3,-Fra3][{-i,-Fra3},{-l,-Fra3}]IntNull[Ns[{k,Fra3},{l,Fra3}]SEpert[LI[o],{i,Fra3},{j,Fra3}]r[]]
											- CDelta[-Fra3,-Fra3][{-i,-Fra3},{-l,-Fra3}]IntNull[Ns[{j,Fra3},{l,Fra3}]SEpert[LI[o],{i,Fra3},{k,Fra3}]r[]]],
Spin[{j_,Fra3},{k_,Fra3}]:>Module[{i,l},-IntNull[SE[{0,Fra},{j,Fra3}] Ns[{k,Fra3}]r[]] + IntNull[SE[{0,Fra},{k,Fra3}]Ns[{j,Fra3}]r[]]
											+CDelta[-Fra3,-Fra3][{-i,-Fra3},{-l,-Fra3}]IntNull[Ns[{k,Fra3},{l,Fra3}]SE[{i,Fra3},{j,Fra3}]r[]]
											- CDelta[-Fra3,-Fra3][{-i,-Fra3},{-l,-Fra3}]IntNull[Ns[{j,Fra3},{l,Fra3}]SE[{i,Fra3},{k,Fra3}]r[]]]
,
Charge[]:>IntNull[SourceDenspert[LI[0]]],
Chargepert[LI[o_]]:>IntNull[SourceDenspert[LI[o]]]
,
ChargeDipole[{b_,basb_}]/;MemberQ[{Fra,Fra3},basb]:>IntNull[Ns[{b,basb}] r[] SourceDenspert[LI[0]]],
ChargeDipolepert[LI[o_],{b_,basb_}]/;MemberQ[{Fra,Fra3},basb]:>IntNull[Ns[{b,basb}] r[] SourceDenspert[LI[o]]]
,
ChargeQuadPole[{b_,basb_},{c_,basc_}]/;And@@(MemberQ[{Fra,Fra3},#]&/@{basb,basc}):>IntNull[r[]^2 Ns[{b,basb},{c,basc}] SourceDenspert[LI[0]]],
ChargeQuadPolepert[LI[o_],{b_,basb_},{c_,basc_}]/;And@@(MemberQ[{Fra,Fra3},#]&/@{basb,basc}):>IntNull[r[]^2 Ns[{b,basb},{c,basc}] SourceDenspert[LI[o]]]};


ReverseBodyParams[expr_]:=expr/.RevBodyParamSubRule;
