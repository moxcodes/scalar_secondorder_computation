(* ::Package:: *)

SetOptions[$FrontEndSession, NotebookAutoSave -> True]
NotebookSave[]


(* ::Text:: *)
(*IMPORTANT: You will need to set the path for the imports to work - set it to wherever you have placed the full package*)


(*$Path=$Path~Join~{"/path/to/these/files"};*)


$Path=$Path~Join~{"/home/mox/research/emri_project/emri_notebooks/refactored_scalar_computation"};


(* ::Section:: *)
(*General routines*)


(* ::Subsection:: *)
(*Initiation*)


(* ::Subsubsection:: *)
(*Import Calls*)


<<xAct`xTensor`


<<xAct`xCoba`


<<xAct`xPert`


<<xAct`TexAct`


<<"3+1Utils.m"


(* ::Subsubsection:: *)
(*Formatting Calls*)


Unprotect[IndexForm];
IndexForm[LI[x_]]:="("<>ToString[x]<>")";
Protect[IndexForm];


$PrePrint=ScreenDollarIndices;


$DefInfoQ=False;


(* ::Subsubsection:: *)
(*Retarded coordinate definitions and rules*)


<<"Retarded3+1Coords.m"


CD[__][CDelta[__][__]]:=0;


(* ::Section:: *)
(*Physical Tensors in Retarded Basis*)


(* ::Subsection:: *)
(*Integration*)


<<"NullIntegration.m"


CommuteThroughNullInt={PhstrExt,PhstrExtPert,acc,accpert,normp,acc1d,acc1dpert,acc2d,acc2dpert,CDelta[Fra3,Fra3],CDelta[-Fra3,Fra3],CDelta[Fra3,-Fra3],CDelta[-Fra3,-Fra3]};


CommuteThroughNullIntScalar={rp};


CommuteThroughNullIntConst={\[Lambda],\[Epsilon]};


IntegrateByPartsList={SE,SEpert,SourceDens,SourceDenspert};


CommuteThroughSNullInt={ChargeCurrent,ChargeCurrentpert,ChargeDipole,ChargeDipolepert,ChargeQuadPole,ChargeQuadPolepert,acc,acc1d};


SIntExclusion=(SourceDens | SourceDenspert);


(* ::Subsection:: *)
(*Sum rules import*)


<<"Sumrules.m"


(* ::Subsection:: *)
(*Tensor import*)


<<"ScalarTensors.m"


(* ::Subsection:: *)
(*Self field derivation*)


(* ::Text:: *)
(*This import takes a few minutes, due to some internal computations. please be patient. In future releases, I'll include a cache to speed this up if you just want the later results.*)


<<"SelfField.m"


(* ::Subsubsection:: *)
(*Equations of motion - Stress Energy Divergence*)


(* ::Text:: *)
(*So, we need to first expand this out, and split out the components of the uncontracted index.*)


SEDivkCompExact=(((Basis[-b,{k,Fra3}]CD[-a][SE[a,b]])//AbstractToBasis[Ret]//ChangeCovD//AbstractToBasis[Ret]//ExpandAll//Ret31Split)
					//ChristoffelPreCompute)/.RetFrameVectorRules//BasisCanon[NoMetriconVBundle]


SEDiv0FraCompExact=((Ret31Split[Basis[-{b,Ret},{0,Fra}]*(AbstractToBasis[Ret][CD[-a][SE[a,b]]//ChangeCovD]//BreakChristoffel)//ExpandAll]//ChristoffelPreCompute)/.RetFrameVectorRules
			//NoScalar//ExpandAll//BasisCanon[NoMetriconVBundle])


SEDiv0RetCompExact=((Ret31Split[Basis[-{b,Ret},{0,Ret}]*(AbstractToBasis[Ret][CD[-a][SE[a,b]]//ChangeCovD]//BreakChristoffel)//ExpandAll]//ChristoffelPreCompute)/.RetFrameVectorRules
			//NoScalar//ExpandAll//BasisCanon[NoMetriconVBundle])


(* ::Text:: *)
(*I will now try a super brief version:*)


SEConsEqkFra=CD[{-a,-Fra}][SE[{a,Fra},{k,Fra3}]]//Frame31Split//FrameCDtoPD//ToRettauFrameiderivs//ExpandAll


Coefficient[Series[SEConsEqkFra,{\[Epsilon],0,4}],\[Epsilon]^4]//NoScalar


Coefficient[Series[%1433,{\[Epsilon],0,4}],\[Epsilon]^4]//NoScalar//BasisCanon[NoMetriconVBundle]


?ToRettauFrameiderivs


CD[{-a,-Fra}][SE[{a,Fra},{k,Fra3}]]//Frame31Split//FrameCDtoPD//ToRettauFrameiderivs//ExpandAll//Series[#,{\[Epsilon],0,2}]&//Normal//ExpandAll


PD[{-i,-Fra3}][r[]]


Basis[{-i,-Fra3},{j,Ret3}]/.RetFrameVectorRules


SEConsEq0Fra=CD[{-a,-Fra}][SE[{a,Fra},{0,Fra}]]//Frame31Split//FrameCDtoPD//ToRettauFrameiderivs//ExpandAll


Basis[{0,Ret},{-a,-Fra}]SE[{a,Fra},{k,Fra3}]//Frame31Split//RetCanon


(* ::Section:: *)
(*Perturbative Construction*)


(* ::Subsection:: *)
(*Rule generation*)


<<"scalarRuleGeneration.m"


(* ::Subsection:: *)
(*Perturbative definitions*)


NZkFraSECons=((SEConsEqkFra - \[Epsilon] SourceDens[]PhstrExt[{k,Fra3}])/.PD[{0,-Ret}][tens_]:>\[Epsilon] PD[{0,-Ret}][tens])//Frame31Split//BasisCanon[NoScreenNoMetric];


NZ0FraSECons=((SEConsEq0Fra - \[Epsilon] SourceDens[]PhstrExt[{0,Fra}])/.PD[{0,-Ret}][tens_]:>\[Epsilon] PD[{0,-Ret}][tens])//Frame31Split//BasisCanon[NoScreenNoMetric];


(* ::Subsection:: *)
(*Renormalizing Body Parameters*)


ToHarteSpinMomRules[0]={Mom[a_]:>HMom[a]};


FromHarteSpinMomRules[0]={HMom[a_]:>Mom[a]};


ToHarteSpinMomRules[1]={Mompert[LI[1],{0,Fra}]:>HMompert[LI[1],{0,Fra}] - Charge[]PD[{0,-Fra}][Charge[]],
					   Mompert[LI[1],{i_,Fra3}]:>Module[{k,l},HMompert[LI[1],{i,Fra3}]
																-(1/3)acc[{i,Fra3}]Charge[]^2],
					   Spin[inds__]:>HSpin[inds]};


FromHarteSpinMomRules[1]={HMompert[LI[1],{0,Fra}]:>Mompert[LI[1],{0,Fra}] + Charge[]PD[{0,-Fra}][Charge[]],
		  				HMompert[LI[1],{i_,Fra3}]:>Module[{k,l},Mompert[LI[1],{i,Fra3}]
																	+(1/3)acc[{i,Fra3}]Charge[]^2],
				  		HSpin[inds__]:>Spin[inds]};


ToHarteSpinMomRules[2]={Mompert[LI[2],{0,Fra}]:>Scalar[HMompert[LI[2],{0,Fra}]
														+ 2 Charge[]PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[{0,Fra}]]]
														-2 PD[{0,-Fra}][PD[{0,-Fra}][Charge[]]]ChargeDipole[{0,Fra}]
														+2 PD[{0,-Fra}][Charge[]]PD[{0,-Fra}][ChargeDipole[{0,Fra}]]
														+(4/3) acc[{-k,-Fra3}] Charge[] PD[{0,-Fra}][ChargeDipole[{k,Fra3}]]
														+(10/3) acc[{-k,-Fra3}] PD[{0,-Fra}][Charge[]] ChargeDipole[{k,Fra3}]
														+2 acc1d[{k,Fra3}] Charge[] ChargeDipole[{l,Fra3}] CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}]
														- 2 Chargepert[LI[1]]PD[{0,-Fra}][Charge[]]
														- 2 Charge[]PD[{0,-Fra}][Chargepert[LI[1]]]],
					   Mompert[LI[2],{i_,Fra3}]:>Module[{k,l},HMompert[LI[2],{i,Fra3}]
																-(2/3)Charge[]PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[{i,Fra3}]]]
																+(2/3) PD[{0,-Fra}][PD[{0,-Fra}][Charge[]]]ChargeDipole[{i,Fra3}]
																-(2/3) PD[{0,-Fra}][Charge[]]PD[{0,-Fra}][ChargeDipole[{i,Fra3}]]
																+(4/3)acc[{i,Fra3}] Charge[] PD[{0,-Fra}][ChargeDipole[{0,Fra}]]
																-2 acc[{i,Fra3}] PD[{0,-Fra}][Charge[]] ChargeDipole[{0,Fra}]
																-(2/15) acc[{-k,-Fra3}] acc[{k,Fra3}] Charge[] ChargeDipole[{i,Fra3}]
																-(2/3) acc1d[{i,Fra3}] Charge[] ChargeDipole[{0,Fra}]
																+(26/15) acc[{-k,-Fra3}]acc[{i,Fra3}] Charge[] ChargeDipole[{k,Fra3}]
																-(4/3)acc[{i,Fra3}]Charge[]Chargepert[LI[1]]],
					   Spinpert[LI[1],{i_,Fra3},{j_,Fra3}]:>Module[{k},HSpinpert[LI[1],{i,Fra3},{j,Fra3}]
															+ (1/3) Charge[] acc[{j,Fra3}] ChargeDipole[{i,Fra3}]
															- (1/3) Charge[] acc[{i,Fra3}] ChargeDipole[{j,Fra3}]],
						Spinpert[LI[1],{i_,Fra3},{0,Fra}]:>Module[{k},HSpinpert[LI[1],{i,Fra3},{0,Fra}]
																	+ (1/3) Charge[] PD[{0,-Fra}][ChargeDipole[{i,Fra3}]]
																	-(1/3) PD[{0,-Fra}][Charge[]] ChargeDipole[{i,Fra3}]],
						Spinpert[LI[1],{0,Fra},{i_,Fra3}]:>Module[{k},HSpinpert[LI[1],{0,Fra},{i,Fra3}]
																	- (1/3) Charge[] PD[{0,-Fra}][ChargeDipole[{i,Fra3}]]
																	+(1/3) PD[{0,-Fra}][Charge[]] ChargeDipole[{i,Fra3}]]
						};


FromHarteSpinMomRules[2]={HMompert[LI[2],{0,Fra}]:>Scalar[Mompert[LI[2],{0,Fra}]
														- 2 Charge[]PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[{0,Fra}]]]
														+2 PD[{0,-Fra}][PD[{0,-Fra}][Charge[]]]ChargeDipole[{0,Fra}]
														-2 PD[{0,-Fra}][Charge[]]PD[{0,-Fra}][ChargeDipole[{0,Fra}]]
														-(4/3) acc[{-k,-Fra3}] Charge[] PD[{0,-Fra}][ChargeDipole[{k,Fra3}]]
														-(10/3) acc[{-k,-Fra3}] PD[{0,-Fra}][Charge[]] ChargeDipole[{k,Fra3}]
														-2 acc1d[{k,Fra3}] Charge[] ChargeDipole[{l,Fra3}] CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}]
														+ 2 Chargepert[LI[1]]PD[{0,-Fra}][Charge[]]
														+ 2 Charge[]PD[{0,-Fra}][Chargepert[LI[1]]]],
		  				HMompert[LI[2],{i_,Fra3}]:>Module[{k,l},Mompert[LI[2],{i,Fra3}]
																+(2/3)Charge[]PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[{i,Fra3}]]]
																-(2/3) PD[{0,-Fra}][PD[{0,-Fra}][Charge[]]]ChargeDipole[{i,Fra3}]
																+(2/3) PD[{0,-Fra}][Charge[]]PD[{0,-Fra}][ChargeDipole[{i,Fra3}]]
																-(4/3)acc[{i,Fra3}] Charge[] PD[{0,-Fra}][ChargeDipole[{0,Fra}]]
																+2 acc[{i,Fra3}] PD[{0,-Fra}][Charge[]] ChargeDipole[{0,Fra}]
																+(2/15) acc[{-k,-Fra3}] acc[{k,Fra3}] Charge[] ChargeDipole[{i,Fra3}]
																+(2/3) acc1d[{i,Fra3}] Charge[] ChargeDipole[{0,Fra}]
																-(26/15) acc[{-k,-Fra3}]acc[{i,Fra3}] Charge[] ChargeDipole[{k,Fra3}]
																+(4/3)acc[{i,Fra3}]Charge[]Chargepert[LI[1]]],
				  		HSpinpert[LI[1],{i_,Fra3},{j_,Fra3}]:>Module[{k},Spinpert[LI[1],{i,Fra3},{j,Fra3}]
															- (1/3) Charge[] acc[{j,Fra3}] ChargeDipole[{i,Fra3}]
															+ (1/3) Charge[] acc[{i,Fra3}] ChargeDipole[{j,Fra3}]],
						HSpinpert[LI[1],{i_,Fra3},{0,Fra}]:>Module[{k},Spinpert[LI[1],{i,Fra3},{0,Fra}]
																	- (1/3) Charge[] PD[{0,-Fra}][ChargeDipole[{i,Fra3}]]
																	+(1/3) PD[{0,-Fra}][Charge[]] ChargeDipole[{i,Fra3}]],
						HSpinpert[LI[1],{0,Fra},{i_,Fra3}]:>Module[{k},Spinpert[LI[1],{0,Fra},{i,Fra3}]
																	+ (1/3) Charge[] PD[{0,-Fra}][ChargeDipole[{i,Fra3}]]
																	-(1/3) PD[{0,-Fra}][Charge[]] ChargeDipole[{i,Fra3}]]};


(* ::Text:: *)
(*After this is run, we'll have to run the full gambit of inverting body params, and re-simplifying them, as we will certainly pick up some factors of the spatial momentum that will almost certainly vanish...*)


SpinSup:={RSpin[{i_,Fra3},{0,Fra}]:>Module[{j,k},0],
		  RSpin[{0,Fra},{i_,Fra3}]:>Module[{j,k},0],
		  RSpinpert[LI[o_],{i_,Fra3},{0,Fra}]:>0,
		  RSpinpert[LI[o_],{0,Fra},{i_,Fra3}]:>0}


FromHarteSpinMom[order_][expr_]:=expr//.(Join@@FromHarteSpinMomRules/@Range[0,order]);


ToHarteSpinMom[order_][expr_]:=expr//.(Join@@ToHarteSpinMomRules/@Range[0,order]);


(* ::Subsubsection:: *)
(*Restricted body parameters*)


(* ::Text:: *)
(*ResDipole - restricted dipole, projected the free index spatially. Explicitly orthogonal to the worldline velocity*)


DefTensor[RCharge[],{M4},PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(q\), \(~\)], \(R\)]\)"];
DefTensorPerturbation[RChargepert[LI[o]],RCharge[],{M4},PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(q\), \(~\)], \(R\)]\)"];


DefTensor[RDipole[a],{M4},PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];
DefTensorPerturbation[RDipolepert[LI[o],a],RDipole[a],{M4},PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];


RDipole[{0,Fra}]:=0;


SubRDipole={ChargeDipole[{i_,Fra3}]:>RDipole[{i,Fra3}],
			  ChargeDipolepert[LI[1],{i_,Fra3}]:>(RDipolepert[LI[1],{i,Fra3}] + (CD[{0,-Fra}][ChargeQuadPole[{i,Fra3},{0,Fra}]]//ScaledFrameCDtoPD))};


SubRCharge={Charge[]:>RCharge[],
			  Chargepert[LI[1]]:>((RChargepert[LI[1]] + CD[{0,-Fra}][ChargeDipole[{0,Fra}]])//ScaledFrameCDtoPD),
			  Chargepert[LI[2]]:>Scalar[(RChargepert[LI[2]] + 2 CD[{0,-Fra}][ChargeDipolepert[LI[1],{0,Fra}]]
												   - 2 acc1d[{-i,-Fra3}]ChargeQuadPole[{0,Fra},{i,Fra3}] 
													- 2 acc[{-i,-Fra3}]PD[{0,-Fra}][ChargeQuadPole[{0,Fra},{i,Fra3}]])]};


DefTensor[RQuadrupole[b,c],{M4},Symmetric[{b,c}],PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];


SubRQuadrupole={ChargeQuadPole[{i_,Fra3},{j_,Fra3}]:>RQuadrupole[{i,Fra3},{j,Fra3}],
					ChargeQuadPole[{0,Fra},{0,Fra}]:>Module[{i,j},RQuadrupole[{i,Fra3},{j,Fra3}]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}]]};


RQuadrupole/:RQuadrupole[{0,Fra},c_]:=0;
RQuadrupole/:RQuadrupole[c_,{0,Fra}]:=0;


DefTensor[RCharge[],{M4},PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(q\), \(~\)], \(R\)]\)"];


DefTensor[RMass[],{M4},PrintAs->"m"];
DefTensorPerturbation[RMasspert[LI[o]],RMass[],{M4},PrintAs->"m"];


InertialMassSub={HMom[{0,Fra}]:>RMass[],
				HMompert[LI[1],{0,Fra}]:>Module[{k,l},RMass[LI[1]] + PhstrExt[{0,Fra}]ChargeDipole[{0,Fra}]],
				HMompert[LI[2],{0,Fra}]:>Module[{j,k,l},RMass[LI[2]] + 2 PhstrExt[{0,Fra}]ChargeDipolepert[LI[1],{0,Fra}]
											+2 ChargeDipole[{0,Fra}]PD[{0,-Fra}][PD[{0,-Fra}][Charge[]]]]
											- 2 acc[{-i,-Fra3}]ChargeQuadPole[{i,Fra3},{0,Fra}]PhstrExt[{0,Fra}] 
											+ 2 CD[{-i,-Fra3}][PhstrExt[{0,Fra}]] ChargeQuadPole[{i,Fra3},{0,Fra}]};


DefTensor[RSpin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(S\), \(~\)], \(R\)]\)"];
DefTensorPerturbation[RSpinpert[LI[o],a,b],RSpin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(S\), \(~\)], \(R\)]\)"];


SubResSpin={HSpinpert[LI[1],{k_,Fra3},{m_,Fra3}]:>Module[{i,j},RSpinpert[LI[1],{k,Fra3},{m,Fra3}]
													+ ChargeQuadPole[{m,Fra3},{0,Fra}]  PhstrExt[{k,Fra3}]
													- ChargeQuadPole[{k,Fra3},{0,Fra}]  PhstrExt[{m,Fra3}]],
			HSpinpert[LI[1],{k_,Fra3},{0,Fra}]:>Module[{i,j},RSpinpert[LI[1],{k,Fra3},{0,Fra}]
												+ ChargeQuadPole[{0,Fra},{0,Fra}]PhstrExt[{k,Fra3}]
												- ChargeQuadPole[{k,Fra3},{0,Fra}] PhstrExt[{0,Fra}]],
			HSpinpert[LI[1],{0,Fra},{k_,Fra3}]:>Module[{i,j},RSpinpert[LI[1],{0,Fra},{k,Fra3}]
												- ChargeQuadPole[{0,Fra},{0,Fra}]PhstrExt[{k,Fra3}]
												+ ChargeQuadPole[{k,Fra3},{0,Fra}] PhstrExt[{0,Fra}]]
};


(* ::Subsubsection:: *)
(*Derivative utilities for multipoles*)


DefTensor[DChargeDipole[b],{M4},PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)Q"];
DefTensor[DDChargeDipole[b],{M4},PrintAs->"\!\(\*SuperscriptBox[SubscriptBox[\(D\), \(\[Tau]\)], \(2\)]\)Q"];
ConvertToDChargeDipole[expr_]:=expr/.{PD[{0,-Fra}][ChargeDipole[inds__]]:>(PD[{0,-Fra}][ChargeDipole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][ChargeDipole[inds__]]:>DChargeDipole[inds]};
ConvertToDDChargeDipole[expr_]:=expr/.{PD[{0,-Fra}][DChargeDipole[inds__]]:>(PD[{0,-Fra}][DChargeDipole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][DChargeDipole[inds__]]:>DDChargeDipole[inds]};


DefTensor[DRDipole[a],{M4},PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];
DefTensor[DDRDipole[a],{M4},PrintAs->"\!\(\*SuperscriptBox[SubscriptBox[\(D\), \(\[Tau]\)], \(2\)]\)\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];
ConvertToDRDipole[expr_]:=expr/.{PD[{0,-Fra}][RDipole[inds__]]:>(PD[{0,-Fra}][RDipole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][RDipole[inds__]]:>DRDipole[inds]};
ConvertToDDRDipole[expr_]:=expr/.{PD[{0,-Fra}][DRDipole[inds__]]:>(PD[{0,-Fra}][DRDipole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][DRDipole[inds__]]:>DDRDipole[inds]};


FullConvertToDRDipole[n_][expr_]:=(expr//Nest[(#//ConvertToDRDipole//BasisCanon[NoMetriconVBundle])&,#,n]&
										 //Nest[(#//ConvertToDDRDipole//BasisCanon[NoMetriconVBundle])&,#,n-1]&
										//Nest[(#//ConvertToDRDipole//BasisCanon[NoMetriconVBundle])&,#,n-2]&);


DRDipole[{0,Fra}]:=Module[{k},acc[{-k,-Fra3}]RDipole[{k,Fra3}]];
DDRDipole[{0,Fra}]:=Module[{k},acc1d[{-k,-Fra3}]RDipole[{k,Fra3}]];


DefTensor[DChargeQuadrupole[b,c],{M4},Symmetric[{b,c}],PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)Q"];
DefTensor[DDChargeQuadrupole[b,c],{M4},Symmetric[{b,c}],PrintAs->"\!\(\*SuperscriptBox[SubscriptBox[\(D\), \(\[Tau]\)], \(2\)]\)Q"];
ConvertToDChargeQuadrupole[expr_]:=expr/.{PD[{0,-Fra}][ChargeQuadPole[inds__]]:>(PD[{0,-Fra}][ChargeQuadPole[inds]]
									//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][ChargeQuadPole[inds__]]:>DChargeQuadrupole[inds]};
ConvertToDDChargeQuadrupole[expr_]:=expr/.{PD[{0,-Fra}][DChargeQuadrupole[inds__]]:>(PD[{0,-Fra}][DChargeQuadrupole[inds]]
									//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][DChargeQuadrupole[inds__]]:>DDChargeQuadrupole[inds]};


DefTensor[DRQuadrupole[b,c],{M4},Symmetric[{b,c}],PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];
DefTensor[DDRQuadrupole[b,c],{M4},Symmetric[{b,c}],PrintAs->"\!\(\*SuperscriptBox[SubscriptBox[\(D\), \(\[Tau]\)], \(2\)]\)\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];
ConvertToDRQuadrupole[expr_]:=expr/.{PD[{0,-Fra}][RQuadrupole[inds__]]:>(PD[{0,-Fra}][RQuadrupole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][RQuadrupole[inds__]]:>DRQuadrupole[inds]};
ConvertToDDRQuadrupole[expr_]:=expr/.{PD[{0,-Fra}][DRQuadrupole[inds__]]:>(PD[{0,-Fra}][DRQuadrupole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][DRQuadrupole[inds__]]:>DDRQuadrupole[inds]};


FullConvertToDRQuadrupole[n_][expr_]:=(expr//Nest[(#//ConvertToDRQuadrupole//BasisCanon[NoMetriconVBundle])&,#,n]&
										 //Nest[(#//ConvertToDDRQuadrupole//BasisCanon[NoMetriconVBundle])&,#,n-1]&
										//Nest[(#//ConvertToDRQuadrupole//BasisCanon[NoMetriconVBundle])&,#,n-2]&);


DefTensor[DPhstrExt[b,c],{M4}];
CovDPhstrext[expr_]:=((expr/.{CD[a_][PhstrExt[inds__]]:>DPhstrExt[a,inds]}
					 /.{PD[a_][DPhstrExt[inds__]]:>(PD[a][DPhstrExt[inds]]//ScaledFramePDtoCD),
						PD[a_][PD[b_][PhstrExt[inds__]]]:>(PD[a][PD[b][PhstrExt[inds]]]//ScaledFramePDtoCD),
						PD[a_][PhstrExt[inds__]]:>(PD[a][PhstrExt[inds]]//ScaledFramePDtoCD)}/.{DPhstrExt[a_,b_]:>CD[a][PhstrExt[b]]})
					/.{CD[{i_,-Fra3}][CD[{0,-Fra}][PhstrExt[ind_]]]:>CD[{0,-Fra}][CD[{i,-Fra3}][PhstrExt[ind]]]});


(* ::Subsection:: *)
(*Cascaded rule generation and application*)


ClearAll[NZEoMRules];
ClearAll[NZSumEoMRules];
ClearAll[NZUnprocRules];
ClearAll[NZDerivRules];


NZDerivRules[n_]={};
NZUnprocRules[n_]={};
NZSumEoMRules[n_]={};
NZEoMRules[n_]={};


ClearAll[GeneratedDerivRules]


GeneratedDerivRules[_]:={};


ApplyEoMRules[mm_?IntegerQ][expr_]:=Module[{TempExpr=expr,ii,NewTempExpr},
	For[ii=mm,ii>=0,ii--,
		NewTempExpr=TempExpr/.NZEoMRules[ii]//ExpandAll;
		NewTempExpr=NewTempExpr//ApplySumRuleList[NZSumEoMRules[ii]]//ExpandAll;
		While[!(NewTempExpr===TempExpr),
			TempExpr=NewTempExpr;
			NewTempExpr=TempExpr/.NZEoMRules[ii]//ExpandAll;
			NewTempExpr=NewTempExpr//ApplySumRuleList[NZSumEoMRules[ii]]//ExpandAll;];
	];
	Return[TempExpr//BasisCanon[NoScreenNoMetric]];];


RepeatedApplyAllBodyParams[maxRepeats_][expr_]:=Module[{TempExpr=expr,ii,NewTempExpr},
				NewTempExpr=(TempExpr//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams);
				For[ii=0,ii<maxRepeats,ii++,
					If[NewTempExpr==TempExpr,Return[NewTempExpr];];
					TempExpr=NewTempExpr;
					NewTempExpr=(TempExpr//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams);];
				Return[NewTempExpr];];


ApplyAllRules[order_][expr_]:=Module[{TempExpr=expr,ii,NewTempExpr},
		NewTempExpr=(TempExpr/.Join@@(MomRules[#]&/@Range[0,order])//ExpandAll);
		For[ii=0,ii<order,ii++,
			NewTempExpr=(NewTempExpr//ApplyEoMRules[order]//ApplyAllBodyParams)/.SIntNullRules/.Join@@(MomRules[#]&/@Range[0,order]);];
		NewTempExpr=NewTempExpr//ApplyEoMRules[order]//ApplyAllBodyParams;
	Return[NewTempExpr//BasisCanon[NoScreenNoMetric]];];


DiscardInvR:={R[]^n_/;n<0:>0};


(* ::Subsection:: *)
(*General evaluation functions*)


MaxOrder=3;


KleinGordonFra=(met[a,b]CD[-a][Phstr[-b]])//AbstractToBasis[Fra]//Frame31Split//ScaleDerivs//ScaledFrameCDtoPD;


NZ0FraSEConsOrder[0]:=NZ0FraSECons/.\[Epsilon]->0;
NZ0FraSEConsOrder[order_?IntegerQ]/;order>0:=(Perturb[(NZ0FraSECons),order]//ExpandAll//Series[#,{\[Epsilon],0,order}]&//Coefficient[#,\[Epsilon]^order]&)//ExpandAll//NoScalar;
NZkFraSEConsOrder[0]:=NZkFraSECons/.\[Epsilon]->0;
NZkFraSEConsOrder[order_?IntegerQ]/;order>0:=(Perturb[(NZkFraSECons),order]//ExpandAll//Series[#,{\[Epsilon],0,order}]&//Coefficient[#,\[Epsilon]^order]&)//ExpandAll//NoScalar;


NZ0FraSEConsOrderMoment[order_?IntegerQ][NsMoment_?IntegerQ][rMoment_?IntegerQ]/;order>0:=((((
			(IntNull[((NZ0FraSECons * r[]^rMoment * (Ns[Sequence@@({#,Fra3}&/@(Unique/@(n&/@Range[NsMoment])))]))//Perturb[#,order]&//ExpandAll
				//Series[#,{\[Epsilon],0,order}]&//Normal)/.ApplyPtoPhstrExt]//NoScalar)//.nstoNsrule//.NullIntparts//.nstoNsrule)//ExpandAll//Coefficient[#,\[Epsilon]^order]&)
				/.SurfaceFieldRules)//Map[(BasisCanon[NoScreenNoMetric][Expand[#]]&),#]&//BasisCanon[NoMetriconVBundle]);
NZ0FraSEConsOrderMoment[0][NsMoment_?IntegerQ][rMoment_?IntegerQ]:=(((
			((IntNull[((NZ0FraSECons * r[]^rMoment * (Ns[Sequence@@({#,Fra3}&/@(Unique/@(n&/@Range[NsMoment])))]))//ExpandAll//Normal)/.\[Epsilon]->0]//NoScalar)//.nstoNsrule
				//.NullIntparts//.nstoNsrule)//ExpandAll)/.\[Epsilon]->0/.SurfaceFieldRules)//Map[(BasisCanon[NoScreenNoMetric][Expand[#]]&),#]&//BasisCanon[NoMetriconVBundle]);
NZkFraSEConsOrderMoment[order_?IntegerQ][NsMoment_?IntegerQ][rMoment_?IntegerQ]/;order>0:=((((
			(IntNull[((NZkFraSECons * r[]^rMoment * (Ns[Sequence@@({#,Fra3}&/@(Unique/@(n&/@Range[NsMoment])))]))//Perturb[#,order]&//ExpandAll
				//Series[#,{\[Epsilon],0,order}]&//Normal)/.ApplyPtoPhstrExt]//NoScalar)//.nstoNsrule//.NullIntparts//.nstoNsrule)//ExpandAll//Coefficient[#,\[Epsilon]^order]&)
				/.SurfaceFieldRules)//Map[(BasisCanon[NoScreenNoMetric][Expand[#]]&),#]&//BasisCanon[NoMetriconVBundle]);
NZkFraSEConsOrderMoment[0][NsMoment_?IntegerQ][rMoment_?IntegerQ]:=(((
			((IntNull[((NZkFraSECons * r[]^rMoment * (Ns[Sequence@@({#,Fra3}&/@(Unique/@(n&/@Range[NsMoment])))]))//ExpandAll//Normal)/.\[Epsilon]->0]//NoScalar)//.nstoNsrule
				//.NullIntparts//.nstoNsrule)//ExpandAll)/.\[Epsilon]->0/.SurfaceFieldRules)//Map[(BasisCanon[NoScreenNoMetric][Expand[#]]&),#]&//BasisCanon[NoMetriconVBundle]);


NZ0FraSEConsOrderMomentEoM[order_?IntegerQ][NsMoment_?IntegerQ][rMoment_?IntegerQ]:=((NZ0FraSEConsOrderMoment[order][NsMoment][rMoment]//ApplyEoMRules[order])/.SIntNullRules);
NZkFraSEConsOrderMomentEoM[order_?IntegerQ][NsMoment_?IntegerQ][rMoment_?IntegerQ]:=((NZkFraSEConsOrderMoment[order][NsMoment][rMoment]//ApplyEoMRules[order])/.SIntNullRules);


TidyPhstrToPhstrReg[expr_]:=(expr/.{Phstrpert->RegPhstrpert,Phstr[__]:>0})/.{RegPhstrpert[LI[n_?IntegerQ],inds__]:>RegPhstrpert[LI[{n,0}],inds]}/.{RegPhstrpert[LI[{n_,a_}],inds__]/;n<2:>0};


(* ::Text:: *)
(*Note that the scaling here is not strictly valid in complete generality - the conversion of i derivatives acting on body params can give promotion, *)
(*	but this is not an important effect for this expression as all orders lower than 2 explicitly vanish.*)


(* ::Text:: *)
(*TODO: Find somewhere better for this*)


(* ::Text:: *)
(*At each order, we'd like to confirm the maxwell field equation through  1/r^3-order *)


KleinGordonFraConfirmation[0]:=(((Qerturb[Perturb[KleinGordonFra,0],3]//ExpandAll)/.{Phstr[__]:>0,Phstrpert[LI[n_?IntegerQ],__]:>0,q->1}/.{\[Epsilon]:>0}
														/.PhstrfieldRulespert//ExpandAll)/.{\[Epsilon]:>0}//BasisCanon[NoScreenNoMetric]//ReverseBodyParams
														//ApplyEoMRules[0]//ApplyAllBodyParams)/.{\[Epsilon]:>0};
KleinGordonFraConfirmation[order_?IntegerQ]/;order>0:=(((Qerturb[Perturb[KleinGordonFra,order],3-order]//ExpandAll)/.{Phstr[__]:>0,Phstrpert[LI[n_?IntegerQ],__]:>0,q->1}/.{\[Epsilon]^n_/;n>order:>0}
														/.PhstrfieldRulespert//ExpandAll)//BasisCanon[NoScreenNoMetric]//ReverseBodyParams
														//ApplyEoMRules[order]//ApplyAllBodyParams);


RegenEoMs=True;


OmitMomentumFromRules=True;


(* ::Section:: *)
(*Order-by-order field equation expansion*)


(* ::Subsection:: *)
(*0th-order computations*)


(* ::Subsubsection:: *)
(*0th - Order Computations  - Spatial Components*)


(* ::Text:: *)
(*Uncomment to print them all:*)


(*For[inti=0,inti<=4,inti++,
For[intj=0,intj<=4,intj++,
Print["----"];
Print[NZkFraSEConsOrderMomentEoM[0][inti][intj]//ScreenDollarIndices//Timing];
Print["======"];
Print[NZkFraSEConsOrderMoment[0][inti][intj]//ScreenDollarIndices//Timing];
];
];//Timing*)


MomRules[0]={};
tempEoM=NZkFraSEConsOrderMomentEoM[0][0][1];
For[ii=0,ii<=3,ii++,
	MomRules[0]=MomRules[0]~Join~GenerateRulesFromEoM[Nest[PD[{0,-Fra}],tempEoM,ii]//ExpandAll//GenerateNewDummies];];//Timing


BodyParamLawsRules[0]={};


(* ::Text:: *)
(*This would be a good candidate for parallelization, but so far it seems like xTensor breaks under standard mathematica parallelization methods*)


If[!FileExistsQ["~/.ScalarSelfForceCache/NZEoMRulesScalar0spac.mx"]||!FileExistsQ["~/.ScalarSelfForceCache/NZSumEoMRulesScalar0spac.mx"]||RegenEoMs,
For[inti=0,inti<=3,inti++,
For[intj=0,intj<=3,intj++,
tempEoM=NZkFraSEConsOrderMomentEoM[0][inti][intj];
For[intk=3,intk>=0,intk--,
	If[!(inti===0 &&intj===1 &&OmitMomentumFromRules),
		NZEoMRules[0]=DeleteDuplicates[NZEoMRules[0]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
		NZSumEoMRules[0]=DeleteDuplicates[NZSumEoMRules[0]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	];
];
];
];
DumpSave["~/.ScalarSelfForceCache/NZEoMRulesScalar0spac.mx",NZEoMRules];
DumpSave["~/.ScalarSelfForceCache/NZSumEoMRulesScalar0spac.mx",NZSumEoMRules];
,
DumpGet["~/.ScalarSelfForceCache/NZEoMRulesScalar0spac.mx"];
DumpGet["~/.ScalarSelfForceCache/NZSumEoMRulesScalar0spac.mx"];
];//Timing


(* ::Subsubsection:: *)
(*0th - Order Computations  - Time component*)


(* ::Text:: *)
(*Function to print them all:*)


(*For[inti=0,inti<=3,inti++,
For[intj=0,intj<=3,intj++,
Print["----"];
Print[NZ0FraSEConsOrderMomentEoM[0][inti][intj]//ScreenDollarIndices//Timing];
Print["===="];
Print[NZ0FraSEConsOrderMoment[0][inti][intj]//ScreenDollarIndices//Timing];
];
];//Timing*)


(* ::Text:: *)
(*Otherwise, just go ahead and evaluate each, and take what we can for the rules:*)


tempEoM1=NZ0FraSEConsOrderMoment[0][1][1];
tempEoM2=NZ0FraSEConsOrderMoment[0][0][1];
For[ii=0,ii<=3,ii++,
MomRules[0]=(MomRules[0]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM1,ii])//GenerateNewDummies]
						~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM2,ii])//GenerateNewDummies]);
];


If[!FileExistsQ["~/.ScalarSelfForceCache/NZEoMRulesScalar0time.mx"]||!FileExistsQ["~/.ScalarSelfForceCache/NZSumEoMRulesScalar0time.mx"]||RegenEoMs,
For[inti=0,inti<=3,inti++,
For[intj=0,intj<=3,intj++,
tempEoM=NZ0FraSEConsOrderMomentEoM[0][inti][intj];
For[intk=3,intk>=0,intk--,
If[!(((inti===1 &&intj===1)||(inti===0 &&intj===1)) &&OmitMomentumFromRules),		
	NZEoMRules[0]=DeleteDuplicates[NZEoMRules[0]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[0]=DeleteDuplicates[NZSumEoMRules[0]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
(*NZDerivRules[0]=DeleteDuplicates[NZDerivRules[0]~Join~GenerateRulesFromEoM[(NZ0FraSEConsOrderMoment[0][inti][intj])//GenerateNewDummies]];*)
];
];
];
];
DumpSave["~/.ScalarSelfForceCache/NZEoMRulesScalar0time.mx",NZEoMRules];
DumpSave["~/.ScalarSelfForceCache/NZSumEoMRulesScalar0time.mx",NZSumEoMRules];
,
DumpGet["~/.ScalarSelfForceCache/NZEoMRulesScalar0time.mx"];
DumpGet["~/.ScalarSelfForceCache/NZDerivRulesScalar0time.mx"];
];//Timing


GeneratedMomentumRules={};GeneratedMomentumSumRules={};
baseMomExpression0=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{0,Fra}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[0])/.MomRules[0];
baseMomExpressionk=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{k,Fra3}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[0])/.MomRules[0];
For[ii=0,ii<=3,ii++,
(*Print[ii];*)
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpression0,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[0],{0,Fra}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpressionk,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[0],{k,Fra3}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
];//Timing


GeneratedSpinRules={};GeneratedSpinSumRules={};
(*baseSpinExpression0i=(((Spinpert[LI[1],{k,Fra3},{0,Fra}]//ReverseBodyParams//ApplyEoMRules[1])/.MomRules[0]/.MomRules[1])
								-(((Spinpert[LI[1],{k,Fra3},{0,Fra}]//Renormalize[3])/.SpinSup)//RevRenormalize[3]//ExpandAll//ReverseBodyParams//ExpandAll)/.MomRules[0]/.MomRules[1]//ApplyEoMRules[1]);*)
baseSpinExpression0i=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{0,Fra}]r[]Ns[{l,Fra3}]] - IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{l,Fra3}]r[]]
														//Frame31Split)/.RetFrameVectorRules//.nstoNsrule/.MomRules[0])//ApplyEoMRules[0]);
baseSpinExpressionij=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{k,Fra3}]r[]Ns[{l,Fra3}]] - IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{l,Fra3}]r[]Ns[{k,Fra3}]]
														//Frame31Split)/.RetFrameVectorRules//.nstoNsrule)/.MomRules[0]//ApplyEoMRules[0]);
For[ii=0,ii<=3,ii++,
(*derivedSpinExpression=(Nest[PD[{0,-Fra}],baseSpinExpression0i,ii]);
GeneratedSpinRules=GeneratedSpinRules~Join~GenerateRulesFromEoM[derivedSpinExpression];
GeneratedSpinSumRules=GeneratedSpinSumRules~Join~GenerateSumRulesFromEoM[derivedSpinExpression];*)
derivedSpinExpression=(Nest[PD[{0,-Fra}],baseSpinExpression0i,ii]
						-Nest[PD[{0,-Fra}],Spinpert[LI[0],{0,Fra},{l,Fra3}],ii]);
GeneratedSpinRules=GeneratedSpinRules~Join~GenerateRulesFromEoM[derivedSpinExpression];
GeneratedSpinSumRules=GeneratedSpinSumRules~Join~GenerateSumRulesFromEoM[derivedSpinExpression];
derivedSpinExpression=(Nest[PD[{0,-Fra}],baseSpinExpressionij,ii]
						-Nest[PD[{0,-Fra}],Spinpert[LI[0],{k,Fra3},{l,Fra3}],ii]);
GeneratedSpinRules=GeneratedSpinRules~Join~GenerateRulesFromEoM[derivedSpinExpression];
GeneratedSpinSumRules=GeneratedSpinSumRules~Join~GenerateSumRulesFromEoM[derivedSpinExpression];
];


MomentumBodyParamRules={};


MomentumBodyParamRules={HMom[{i_,Fra3}]->((HMom[{i,Fra3}]//FromHarteSpinMom[1]//ReverseBodyParams)//ApplyAllRules[0]),
						Mom[{i_,Fra3}]->((Mom[{i,Fra3}]//ReverseBodyParams)//ApplyAllRules[0])};


RMassRules={};
RevRMassRules={};


RMassRules=RMassRules~Join~
				{RMasspert[LI[0]]->Series[Sqrt[((Perturbed[Scalar[Mom[{0,Fra}]]^2 - CDelta[-Fra3,-Fra3][{-k,-Fra3},{-j,-Fra3}]Mom[{k,Fra3}]Mom[{j,Fra3}],0])
			//ExpandAll//NoScalar)/.MomentumBodyParamRules],{\[Epsilon],0,0}]/.\[Epsilon]->0/.Sqrt[a_^2]:>a//GenerateNewDummies }
RevRMassRules=RevRMassRules~Join~
				{Mom[{0,Fra}]->((RMasspert[LI[0]] - ((RMasspert[LI[0]]/.RMassRules) - Mom[{0,Fra}]))//NoScalar//ReverseBodyParams//BasisCanon[NoScreenNoMetric]//ApplyEoMRules[0])}


ApplyAllBodyParams[expr_]:=(expr/.ChargeMultipoleRules/.GeneratedMomentumRules/.GeneratedSpinRules)//ApplySumRuleList[SpinMomSumRuleList~Join~GeneratedMomentumSumRules~Join~GeneratedSpinSumRules];


(* ::Subsection:: *)
(*1st-order computations*)


(* ::Subsubsection:: *)
(*1st - Order Computations *)


accFull[1]=((((NZkFraSEConsOrderMomentEoM[1][0][0]//ApplyEoMRules[0]))//ApplyAllBodyParams)/.MomRules[0])//ScreenDollarIndices//ScaledFramePDtoCD


(* ::Text:: *)
(*This is true and required playing a few small tricks. The leading momentum vanishes, so this is directly the standard Lorentz force*)


spinExpression=NZkFraSEConsOrderMomentEoM[1][1][1]//ApplyEoMRules[0];


SpinSolution[1]=(((2*Antisymmetrize[spinExpression,IndicesOf[Free][spinExpression]]//BasisCanon[NoMetriconVBundle])/.MomRules[0])//ScreenDollarIndices);


(SpinSolution[1]//GenerateSumRulesFromEoM);


SpinSolution[1]//ApplyAllBodyParams//ScaledFramePDtoCD


(* ::Text:: *)
(*TODO: I think including the several derivatives here is probably a waste of time*)


MomRules[1]={};
tempEoM=NZkFraSEConsOrderMomentEoM[1][0][1];
For[ii=0,ii<=2,ii++,
	MomRules[1]=MomRules[1]~Join~GenerateRulesFromEoM[Nest[PD[{0,-Fra}],tempEoM,ii]//ExpandAll//GenerateNewDummies];];//Timing


(*For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
Print["----"];
Print[NZkFraSEConsOrderMomentEoM[1][inti][intj]//ScreenDollarIndices//Timing];
Print["===="];
Print[NZkFraSEConsOrderMoment[1][inti][intj]//ScreenDollarIndices//Timing];
];
];//Timing*)


If[!FileExistsQ["~/.ScalarSelfForceCache/NZSumEoMRulesScalar1spac.mx"]||!FileExistsQ["~/.ScalarSelfForceCache/NZEoMRulesScalar1spac.mx"]||RegenEoMs,
For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
If[!(((inti===0 &&intj===1)) &&OmitMomentumFromRules),
tempEoM=NZkFraSEConsOrderMomentEoM[1][inti][intj];
For[intk=2,intk>=0,intk--,
	NZEoMRules[1]=DeleteDuplicates[NZEoMRules[1]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[1]=DeleteDuplicates[NZSumEoMRules[1]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
];
];
];
];
DumpSave["~/.ScalarSelfForceCache/NZDSumEoMRulesScalar1spac.mx",NZSumEoMRules];
DumpSave["~/.ScalarSelfForceCache/NZEoMRulesScalar1spac.mx",NZEoMRules];
,
DumpGet["~/.ScalarSelfForceCache/NZDSumEoMRulesScalar1spac.mx"];
DumpGet["~/.ScalarSelfForceCache/NZEoMRulesScalar1spac.mx"];
];//Timing


(* ::Subsubsection:: *)
(*1st - Order computations - time component*)


(* ::Text:: *)
(*(also the covariant derivative is zero due to the vanishing momentum, but that's irritating to automate here, so I'll just leave as is.*)


MdotFull[1]=((NZ0FraSEConsOrderMomentEoM[1][0][0]//ApplyEoMRules[0])//ApplyAllBodyParams)/.MomRules[0]//BasisCanon[NoMetriconVBundle]//ScaledFramePDtoCD


MdotFull[1]=((NZ0FraSEConsOrderMomentEoM[1][0][0]//ApplyEoMRules[0])//ApplyAllBodyParams)/.MomRules[0]//BasisCanon[NoMetriconVBundle]//ScaledFramePDtoCD


For[ii=0,ii<=2,ii++,
MomRules[1]=(MomRules[1]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],NZ0FraSEConsOrderMomentEoM[1][1][1],ii])//GenerateNewDummies]
						~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],NZ0FraSEConsOrderMomentEoM[1][0][1],ii])//GenerateNewDummies]);
];


((Mompert[LI[1],{k,Fra3}]//ReverseBodyParams)/.MomRules[1]//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams//ScaledFramePDtoCD


((HMompert[LI[1],{k,Fra3}]//FromHarteSpinMom[1]//ReverseBodyParams)/.MomRules[1]//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams//ScaledFramePDtoCD


(* ::Text:: *)
(*TODO:These blocks are copy-pasta code, turn it into a function and make things prettier.*)


If[!FileExistsQ["~/.ScalarSelfForceCache/NZEoMRulesScalar1time.mx"]||!FileExistsQ["~/.ScalarSelfForceCache/NZDerivRulesScalar1time.mx"]||RegenEoMs,
For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
If[!(((inti===1 &&intj===1)||(inti===0 &&intj===1)) &&OmitMomentumFromRules),
	tempEoM=NZ0FraSEConsOrderMomentEoM[1][inti][intj];
For[intk=2,intk>=0,intk--,
	NZEoMRules[1]=DeleteDuplicates[NZEoMRules[1]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[1]=DeleteDuplicates[NZSumEoMRules[1]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
(*NZDerivRules[0]=DeleteDuplicates[NZDerivRules[0]~Join~GenerateRulesFromEoM[(NZ0FraSEConsOrderMoment[0][inti][intj])//GenerateNewDummies]];*)
];
];
];
];
DumpSave["~/.ScalarSelfForceCache/NZEoMRulesScalar0time.mx",NZEoMRules];
DumpSave["~/.ScalarSelfForceCache/NZDerivRulesScalar0time.mx",NZDerivRules];
,
DumpGet["~/.ScalarSelfForceCache/NZEoMRulesScalar0time.mx"];
DumpGet["~/.ScalarSelfForceCache/NZDerivRulesScalar0time.mx"];
];//Timing


(* ::Text:: *)
(*TODO: this is copy-pasta code too....*)


MomentumBodyParamRules=MomentumBodyParamRules~Join~{HMompert[LI[1],{i_,Fra3}]->(((HMompert[LI[1],{i,Fra3}]//FromHarteSpinMom[1]//ReverseBodyParams)//ApplyAllRules[1])/.MomentumBodyParamRules)};
MomentumBodyParamRules=MomentumBodyParamRules~Join~{Mompert[LI[1],{i_,Fra3}]->((Mompert[LI[1],{i,Fra3}]//ToHarteSpinMom[1])/.MomentumBodyParamRules)};


baseMomExpression0=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{0,Fra}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[1])/.MomRules[0]/.MomRules[1]/.SIntNullRules//ApplyEoMRules[1];
baseMomExpressionk=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{k,Fra3}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[1])/.MomRules[0]/.MomRules[1]/.SIntNullRules//ApplyEoMRules[1];
For[ii=0,ii<=2,ii++,
(*Print[ii];*)
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpression0,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[1],{0,Fra}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpressionk,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[1],{k,Fra3}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
];


baseSpinExpression0i=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{0,Fra}]r[]Ns[{l,Fra3}]] - IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{l,Fra3}]r[]]
														//Frame31Split)/.RetFrameVectorRules//.nstoNsrule/.MomRules[0]/.MomRules[1])//ApplyEoMRules[1]);
baseSpinExpressionij=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{k,Fra3}]r[]Ns[{l,Fra3}]] - IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{l,Fra3}]r[]Ns[{k,Fra3}]]
														//Frame31Split)/.RetFrameVectorRules//.nstoNsrule)/.MomRules[0]/.MomRules[1]//ApplyEoMRules[1]);
For[ii=0,ii<=2,ii++,
derivedSpinExpression=(Nest[PD[{0,-Fra}],baseSpinExpression0i,ii]
						-Nest[PD[{0,-Fra}],Spinpert[LI[1],{0,Fra},{l,Fra3}],ii]);
GeneratedSpinRules=GeneratedSpinRules~Join~GenerateRulesFromEoM[derivedSpinExpression];
GeneratedSpinSumRules=GeneratedSpinSumRules~Join~GenerateSumRulesFromEoM[derivedSpinExpression];
derivedSpinExpression=(Nest[PD[{0,-Fra}],baseSpinExpressionij,ii]
						-Nest[PD[{0,-Fra}],Spinpert[LI[1],{k,Fra3},{l,Fra3}],ii]);
GeneratedSpinRules=GeneratedSpinRules~Join~GenerateRulesFromEoM[derivedSpinExpression];
GeneratedSpinSumRules=GeneratedSpinSumRules~Join~GenerateSumRulesFromEoM[derivedSpinExpression];
];


((Sqrt[(Perturb[Mom[{0,Fra}]Mom[{0,Fra}] - Mom[{k,Fra3}]CDelta[-Fra3,-Fra3][-{k,Fra3},-{l,Fra3}]Mom[{l,Fra3}],1]
										/.{expr_*Mom[inds__]:>expr*(Mom[inds]/.MomentumBodyParamRules),expr_*Mompert[inds__]:>expr*(Mompert[inds]/.MomentumBodyParamRules)})]
										//Series[#,{\[Epsilon],0,1}]&//Normal)
										/.{Sqrt[Scalar[some_]^2]:>some,(Scalar[some_]^2)^(-1/2):>1/some,Sqrt[some_^2]:>some}//NoScalar//Coefficient[#,\[Epsilon]]&//BasisCanon[NoMetriconVBundle]//GenerateNewDummies)


RMassRules=RMassRules~Join~
				{RMasspert[LI[1]]->((Sqrt[(Perturb[Mom[{0,Fra}]Mom[{0,Fra}] - Mom[{k,Fra3}]CDelta[-Fra3,-Fra3][-{k,Fra3},-{l,Fra3}]Mom[{l,Fra3}],1]
										/.{expr_*Mom[inds__]:>expr*(Mom[inds]/.MomentumBodyParamRules),expr_*Mompert[inds__]:>expr*(Mompert[inds]/.MomentumBodyParamRules)})]
										//Series[#,{\[Epsilon],0,1}]&//Normal)/.{Sqrt[Scalar[some_]^2]:>some,(Scalar[some_]^2)^(-1/2):>1/some,Sqrt[some_^2]:>some}
										//NoScalar//Coefficient[#,\[Epsilon]]&//BasisCanon[NoMetriconVBundle]//GenerateNewDummies)};
RevRMassRules=RevRMassRules~Join~
				{Mompert[LI[1],{0,Fra}]->(((RMasspert[LI[1]] - ((RMasspert[LI[1]]/.RMassRules) - Mompert[LI[1],{0,Fra}])))//NoScalar//BasisCanon[NoMetriconVBundle])};


RMassRules


(* ::Subsection:: *)
(*2nd-order computations*)


(* ::Subsubsection:: *)
(*2nd - Order Computations - spatial*)


accRaw[2]=(((NZkFraSEConsOrderMomentEoM[2][0][0]//ApplyEoMRules[1]//Expand)//RepeatedApplyAllBodyParams[2])/.MomRules[1]/.MomRules[0]
							//ExpandAll//ApplyAllBodyParams//ToHarteSpinMom[1]//BasisCanon[NoMetriconVBundle])


PreRestrictedAcc[2]=(((accRaw[2]/.MomentumBodyParamRules//Expand)
		//Expand//NoScalar//BasisCanon[NoMetriconVBundle])
		/.{PD[ind_][PhstrExt[inds__]]:>(PD[ind][PhstrExt[inds]]//ScaledFramePDtoCD)})//BasisCanon[NoMetriconVBundle]


((-PreRestrictedAcc[2]/.InertialMassSub/.SubRDipole/.SubRCharge//BasisCanon[NoMetriconVBundle])/.{Spin[___,{0,Fra},___]:>0}//ScaledFramePDtoCD)/.{Spin[___,{0,Fra},___]:>0}


(* ::Text:: *)
(*This checks out against the form previous.*)


(*For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
Print["----"];
Print[NZkCompEoM[2][inti][intj]//ScreenDollarIndices];
];
];*)


spinExpression=NZkFraSEConsOrderMomentEoM[2][1][1];


SpinRaw[2]=((2*Antisymmetrize[spinExpression,IndicesOf[Free][spinExpression]]//BasisCanon[NoMetriconVBundle])/.MomRules[0]/.MomRules[1]);


SpinSolution[2]=(SpinRaw[2]//RepeatedApplyAllBodyParams[2]//BasisCanon[NoMetriconVBundle]
					//ToHarteSpinMom[2]//Expand)//BasisCanon[NoMetriconVBundle]


((SpinSolution[2]/.SubResSpin/.{PD[a_][PhstrExt[inds__]]:>(PD[a][PhstrExt[inds]]//ScaledFramePDtoCD)}//BasisCanon[NoMetriconVBundle])
	/.SubRDipole/.SubRQuadrupole)//ExpandAll//ScaledFramePDtoCD//BasisCanon[NoMetriconVBundle]


MomRules[2]={};
tempEoM=NZkFraSEConsOrderMomentEoM[2][0][1];
For[ii=0,ii<=1,ii++,
	MomRules[2]=MomRules[2]~Join~GenerateRulesFromEoM[Nest[PD[{0,-Fra}],tempEoM,ii]//ExpandAll//GenerateNewDummies];];


(*For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
Print["----"];
Print[NZkFraSEConsOrderMomentEoM[1][inti][intj]//ScreenDollarIndices//Timing];
Print["===="];
Print[NZkFraSEConsOrderMoment[1][inti][intj]//ScreenDollarIndices//Timing];
];
];//Timing*)


If[!FileExistsQ["~/.ScalarSelfForceCache/NZSumEoMRulesScalar2spac.mx"]||!FileExistsQ["~/.ScalarSelfForceCache/NZEoMRulesScalar2spac.mx"]||RegenEoMs,
For[inti=0,inti<=1,inti++,
For[intj=0,intj<=1,intj++,
If[!(((inti===0 &&intj===1)) &&OmitMomentumFromRules),
tempEoM=NZkFraSEConsOrderMomentEoM[2][inti][intj];
For[intk=1,intk>=0,intk--,
	Print[{inti,intj,intk}];
	NZEoMRules[2]=DeleteDuplicates[NZEoMRules[2]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[2]=DeleteDuplicates[NZSumEoMRules[2]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
];
];
];
];
DumpSave["~/.ScalarSelfForceCache/NZDSumEoMRulesScalar2spac.mx",NZSumEoMRules];
DumpSave["~/.ScalarSelfForceCache/NZEoMRulesScalar2spac.mx",NZEoMRules];
,
DumpGet["~/.ScalarSelfForceCache/NZDSumEoMRulesScalar2spac.mx"];
DumpGet["~/.ScalarSelfForceCache/NZEoMRulesScalar2spac.mx"];
];//Timing


(* ::Subsubsection:: *)
(*2nd - Order Computation  - Time Component*)


(((NZ0FraSEConsOrderMomentEoM[2][0][0]//ApplyAllBodyParams)/.MomRules[1]//RepeatedApplyAllBodyParams[2]//BasisCanon[NoMetriconVBundle])
	//NoScalar//ExpandAll//ScaledFramePDtoCD)


MdotRaw[2]=((NZ0FraSEConsOrderMomentEoM[2][0][0]//ApplyAllBodyParams)/.MomRules[1]//RepeatedApplyAllBodyParams[2]//BasisCanon[NoMetriconVBundle]
				//ToHarteSpinMom[1]//NoScalar//ExpandAll);


((MdotRaw[2])/.MomentumBodyParamRules//ExpandAll)/.InertialMassSub/.SubRCharge/.{Spin[___,{0,Fra},___]:>0}//BasisCanon[NoMetriconVBundle]//CovDPhstrext//BasisCanon[NoMetriconVBundle]


tempEoM1=NZ0FraSEConsOrderMomentEoM[2][1][1];
tempEoM2=NZ0FraSEConsOrderMomentEoM[2][0][1];
For[ii=0,ii<=1,ii++,
MomRules[2]=(MomRules[2]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM1,ii])//GenerateNewDummies]
						~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM2,ii])//GenerateNewDummies]);
];


MomkComp[2]=((Mompert[LI[2],{k,Fra3}]//ReverseBodyParams)/.MomRules[2]/.MomRules[1]//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams;


((MomkComp[2]//Expand//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle])
		//ExpandAll//NoScalar//BasisCanon[NoMetriconVBundle]
		//BasisCanon[NoMetriconVBundle])


(*CopyToClipboard[TexBreak[TexPrint[(%2666//NoScalar)/.{\[Epsilon]->0}/.{PD->PD}],450]]*)


If[!FileExistsQ["~/.ScalarSelfForceCache/NZEoMRulesScalar2time.mx"]||!FileExistsQ["~/.ScalarSelfForceCache/NZDerivRulesScalar2time.mx"]||RegenEoMs,
For[inti=0,inti<=1,inti++,
For[intj=0,intj<=1,intj++,
If[!(((inti===1 &&intj===1)||(inti===0 &&intj===1)) &&OmitMomentumFromRules),
	tempEoM=NZ0FraSEConsOrderMomentEoM[2][inti][intj];
For[intk=1,intk>=0,intk--,
	NZEoMRules[2]=DeleteDuplicates[NZEoMRules[2]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[2]=DeleteDuplicates[NZSumEoMRules[2]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
(*NZDerivRules[0]=DeleteDuplicates[NZDerivRules[0]~Join~GenerateRulesFromEoM[(NZ0FraSEConsOrderMoment[0][inti][intj])//GenerateNewDummies]];*)
];
];
];
];
DumpSave["~/.ScalarSelfForceCache/NZEoMRulesScalar2time.mx",NZEoMRules];
DumpSave["~/.ScalarSelfForceCache/NZDerivRulesScalar2time.mx",NZDerivRules];
,
DumpGet["~/.ScalarSelfForceCache/NZEoMRulesScalar2time.mx"];
DumpGet["~/.ScalarSelfForceCache/NZDerivRulesScalar2time.mx"];
];//Timing


(* ::Text:: *)
(*The renormalized spatial, second order momentum*)


HMomkComp[2]=((HMompert[LI[2],{k,Fra3}]//FromHarteSpinMom[2]//ReverseBodyParams)/.MomRules[2]/.MomRules[1]//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams;


((1/2)HMomkComp[2]//NoScalar//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle]


-((Spinpert[LI[1],{i,Fra3},{0,Fra}]//ToHarteSpinMom[2])/.SubResSpin//BasisCanon[NoMetriconVBundle])/.{RSpinpert[___,{0,Fra},___]:>0}


MomentumBodyParamRules=MomentumBodyParamRules~Join~{HMompert[LI[2],{k_,Fra3}]->((((((HMompert[LI[2],{k,Fra3}]//FromHarteSpinMom[2]//ReverseBodyParams)/.MomRules[2]/.MomRules[1])
												//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams)//NoScalar
												//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle]//ToHarteSpinMom[2]//ExpandAll)
												/.SubResSpin//ExpandAll//BasisCanon[NoMetriconVBundle])/.{PD[a_][PhstrExt[inds__]]:>(PD[a][PhstrExt[inds]]//ScaledFramePDtoCD)}
												//BasisCanon[NoMetriconVBundle]};


MomentumBodyParamRules=MomentumBodyParamRules~Join~{Mompert[LI[2],{k_,Fra3}]->((Mompert[LI[2],{k,Fra3}]//ToHarteSpinMom[2])/.MomentumBodyParamRules//GenerateNewDummies)};


baseMomExpression0=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[2],{a,Fra},{0,Fra}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[2])/.MomRules[2]/.MomRules[1]/.MomRules[0]/.SIntNullRules//ApplyEoMRules[2];
baseMomExpressionk=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{k,Fra3}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[1])/.MomRules[2]/.MomRules[1]/.MomRules[0]/.SIntNullRules//ApplyEoMRules[2];
For[ii=0,ii<=1,ii++,
(*Print[ii];*)
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpression0,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[2],{0,Fra}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpressionk,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[2],{k,Fra3}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
];


RMass[2]=(((((2*Sqrt[(Perturb[HMom[{0,Fra}]HMom[{0,Fra}] - HMom[{k,Fra3}]CDelta[-Fra3,-Fra3][-{k,Fra3},-{l,Fra3}]HMom[{l,Fra3}],2]
										/.{expr_*HMom[inds__]:>expr*(HMom[inds]/.MomentumBodyParamRules),expr_*HMompert[inds__]:>expr*(HMompert[inds]/.MomentumBodyParamRules)}
										//GenerateNewDummies)/.MomentumBodyParamRules
										//FromHarteSpinMom[2]])//Series[#,{\[Epsilon],0,2}]&//Normal)
										//NoScalar//Coefficient[#,\[Epsilon]^2]&//BasisCanon[NoMetriconVBundle])
										/.{Sqrt[Scalar[some_]^2]:>some,(Scalar[some_]^2)^(-1/2):>1/some,Sqrt[some_^2]:>some,Scalar[some_]:>(some//GenerateNewDummies)})
										/.{Spin[___,{0,Fra},___]:>0})


CopyToClipboard[TexBreak[TexPrint[((%2114)//Expand)/.{\[Epsilon]->0}/.{PD->PD}],450]]


RMassRules=RMassRules~Join~
				{RMasspert[LI[2]]->RMass[2]};//Timing
RevRMassRules=RevRMassRules~Join~
				{Mompert[LI[2],{0,Fra}]->(((RMasspert[LI[2]] - ((RMasspert[LI[2]]/.RMassRules) - Mompert[LI[2],{0,Fra}])))//NoScalar//BasisCanon[NoMetriconVBundle])};


RMassRules


(* ::Subsection:: *)
(*Regular Field Components*)


(* ::Text:: *)
(*Leading field strength renormalization - confirmation of prior result*)


(1/2)(RegPhstrpert[LI[{2,0}],{-0,-Fra}]/.RegPhstrfieldRulespert)


(1/2)(RegPhstrpert[LI[{2,0}],{-i,-Fra3}]/.RegPhstrfieldRulespert)//BasisCanon[NoMetriconVBundle]


Q[SourceDens[]]:=0;


(* ::Text:: *)
(*Note that the scaling here is not strictly valid in complete generality - the conversion of i derivatives acting on body params can give promotion, *)
(*	but this is not an important effect for this expression as all orders lower than 2 explicitly vanish.*)


kRenormGen=(IntNull[(Phstr[{-k,-Fra3}]SourceDens[]//Perturb[#,3]&//Qerturb[#,1]&)/.q->1]//Frame31Split//ExpandAll//TidyPhstrToPhstrReg)/.{\[Epsilon]^n_/;n>3:>0}


RenormGen0=(IntNull[(Phstr[{0,-Fra}]SourceDens[]//Perturb[#,3]&//Qerturb[#,1]&)/.q->1]//Frame31Split//ExpandAll//TidyPhstrToPhstrReg)/.{\[Epsilon]^n_/;n>3:>0}


IntNull[tens_[inds___]expr_]/;MemberQ[$BodyParams,tens]:=tens[inds]*IntNull[expr];
IntNull[PD[a_][tens_[inds___]]expr_]/;MemberQ[$BodyParams,tens]:=PD[a][tens[inds]]*IntNull[expr];
IntNull[PD[b_][PD[a_][tens_[inds___]]]expr_]/;MemberQ[$BodyParams,tens]:=PD[b][PD[a][tens[inds]]]*IntNull[expr];
IntNull[PD[c_][PD[b_][PD[a_][tens_[inds___]]]]expr_]/;MemberQ[$BodyParams,tens]:=PD[c][PD[b][PD[a][tens[inds]]]]*IntNull[expr];


kRenormExpanded=((kRenormGen/.RegPhstrfieldRulespert/.ConvertScalediFraDerivs)/.{\[Epsilon]^n_/;n>3->0,PD[_][acc2d[__]]:>0}/.nstoNsrule//ExpandAll
			//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams);//Timing


RenormExpanded0=((RenormGen0/.RegPhstrfieldRulespert/.ConvertScalediFraDerivs)/.{\[Epsilon]^n_/;n>3->0,PD[_][acc2d[__]]:>0}/.nstoNsrule//ExpandAll
			//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams);//Timing


RenormExpanded0


kRenormExpanded


((kRenormExpanded//BasisCanon[NoMetriconVBundle])/.MomRules[2]//BasisCanon[NoMetriconVBundle]
	//ExpandAll//NoScalar//BasisCanon[NoMetriconVBundle])//BasisCanon[NoMetriconVBundle]


HMompert[LI[2],{k,Fra3}]//FromHarteSpinMom[2]//NoScalar//BasisCanon[NoMetriconVBundle]


((RenormExpanded0//BasisCanon[NoMetriconVBundle])/.MomRules[2]//BasisCanon[NoMetriconVBundle]
		//ExpandAll//NoScalar//BasisCanon[NoMetriconVBundle])//BasisCanon[NoMetriconVBundle]


HMompert[LI[2],{0,Fra}]//FromHarteSpinMom[2]//NoScalar//BasisCanon[NoMetriconVBundle]


(* ::Subsection:: *)
(*3rd-order computations*)


(* ::Subsubsection:: *)
(*3rd - Order Computations *)


accRaw[3]=NZkFraSEConsOrderMomentEoM[3][0][0];//Timing


-((((accRaw[3]//ApplySumRuleList[MomentumSumRuleList]//ApplyAllBodyParams)
		/.MomRules[2]//BasisCanon[NoMetriconVBundle])//NoScalar
		//BasisCanon[NoMetriconVBundle])//ConvertToDChargeDipole//Expand//ConvertToDChargeDipole//ScaledFramePDtoCD
		//BasisCanon[NoMetriconVBundle])//BasisCanon[NoMetriconVBundle]


accRenorm[3]=-((accRaw[3]//ApplySumRuleList[MomentumSumRuleList]//ApplyAllBodyParams)
		/.MomRules[2]//BasisCanon[NoMetriconVBundle]//ToHarteSpinMom[2])//NoScalar//BasisCanon[NoMetriconVBundle]


PD[{-i,-Ret3}][r[]^3 norm[{k,Fra3}]]//BasisCanon[NoMetriconVBundle]


ChargeDipolepert[LI[1],{i,Fra3}]/.SubRDipole


(Chargepert[LI[2]]/.SubRCharge//NoScalar)/.SubRDipole


PD[{0,-Ret}][acc[{i,Fra3}]]


((-(1/2)Mompert[LI[2],{0,Fra}]//ToHarteSpinMom[2]//NoScalar//BasisCanon[NoMetriconVBundle])/.InertialMassSub//BasisCanon[NoMetriconVBundle]
		//ConvertToDChargeDipole//BasisCanon[NoMetriconVBundle]//ConvertToDChargeDipole//ConvertToDDChargeDipole//BasisCanon[NoMetriconVBundle])


CopyToClipboard[TexBreak[TexPrint[(%492//NoScalar)/.{PD->PD}],450]]


-(Spinpert[LI[1],{i,Fra3},{j,Fra3}]//ToHarteSpinMom[2])/.SubResSpin//BasisCanon[NoMetriconVBundle]//ScaledFramePDtoCD//BasisCanon[NoMetriconVBundle]


CopyToClipboard[TexBreak[TexPrint[(%494//NoScalar)/.{PD->PD}],450]]


-(Spinpert[LI[1],{i,Fra3},{0,Fra}]//ToHarteSpinMom[2])/.SubResSpin//BasisCanon[NoMetriconVBundle]//ScaledFramePDtoCD//BasisCanon[NoMetriconVBundle]


accExpanded[3]=((accRenorm[3]//GenerateNewDummies)/.MomentumBodyParamRules)//ExpandAll//CovDPhstrext//BasisCanon[NoMetriconVBundle];


CopyToClipboard[TexBreak[TexPrint[(%495//NoScalar)/.{PD->PD}],450]]


(* ::Text:: *)
(*Exclusively the new dipole contributions:*)


((((accExpanded[3]//ToHarteSpinMom[2])
		/.InertialMassSub/.SubRCharge/.SubRDipole/.SubResSpin/.SpinSup//ExpandAll//FullConvertToDRDipole[5]))
		/.{PD[a_][DDRDipole[inds__]]:>(PD[a][DDRDipole[inds]]//ScaledFramePDtoCD)}
		/.{(RDipolepert|ChargeDipolepert|ChargeQuadPole|RSpinpert)[__]:>0})//BasisCanon[NoMetriconVBundle]


(* ::Text:: *)
(*Exclusively the new quadrupole contributions:*)


((accExpanded[3]//ToHarteSpinMom[2])
		/.InertialMassSub/.SubRCharge/.SubRDipole/.SubResSpin/.SpinSup/.SubRQuadrupole//CovDPhstrext
    	//NoScalar//FullConvertToDRQuadrupole[3]//BasisCanon[NoMetriconVBundle]
		)/.{(RDipole|RDipolepert|RSpinpert|RCharge|RChargepert|ChargeDipolepert)[__]:>0}


(* ::Subsubsection:: *)
(*3rd - Order Computation  - Time Component*)


DumpGet["MdotRawEM.mx"]


MdotRaw[3]=NZ0FraSEConsOrderMomentEoM[3][0][0];//Timing


MdotRenorm[3]=-((MdotRaw[3]//ApplySumRuleList[MomentumSumRuleList]//ApplyAllBodyParams)
		/.MomRules[2]//BasisCanon[NoMetriconVBundle]//ToHarteSpinMom[2])//NoScalar//BasisCanon[NoMetriconVBundle]


((MdotRenorm[3]//ConvertToDChargeDipole//BasisCanon[NoMetriconVBundle]//ConvertToDChargeDipole//BasisCanon[NoMetriconVBundle]
	//ConvertToDChargeDipole//BasisCanon[NoMetriconVBundle]//ConvertToDDChargeDipole)//BasisCanon[NoMetriconVBundle]//ConvertToDDChargeDipole
	//BasisCanon[NoMetriconVBundle])/.{PD[a_][DDChargeDipole[b_]]:>(PD[a][DDChargeDipole[b]]//ScaledFramePDtoCD)}//BasisCanon[NoMetriconVBundle]


CopyToClipboard[TexBreak[TexPrint[(%2027//NoScalar)/.{\[Epsilon]->0}/.{PD->PD}],450]]


MdotExpanded[3]=((MdotRenorm[3]//GenerateNewDummies)/.MomentumBodyParamRules)//ExpandAll//CovDPhstrext//BasisCanon[NoMetriconVBundle];


(* ::Text:: *)
(*Just the dipole dependence:*)


((((MdotExpanded[3]//ToHarteSpinMom[2])
		/.InertialMassSub/.SubRCharge/.SubRDipole/.SubResSpin/.SpinSup//ExpandAll//FullConvertToDRDipole[5]))
		/.{PD[a_][DDRDipole[inds__]]:>(PD[a][DDRDipole[inds]]//ScaledFramePDtoCD)}
		/.{(RDipolepert|ChargeDipolepert|ChargeQuadPole|RSpinpert)[__]:>0})//BasisCanon[NoMetriconVBundle]


(* ::Text:: *)
(*Just the quadrupole dependence:*)


((MdotExpanded[3]//ToHarteSpinMom[2])
		/.InertialMassSub/.SubRCharge/.SubRDipole/.SubResSpin/.SpinSup/.SubRQuadrupole//CovDPhstrext
    	//NoScalar//FullConvertToDRQuadrupole[3]//BasisCanon[NoMetriconVBundle]
		)/.{(RDipole|RDipolepert|RSpinpert|RCharge|RChargepert|ChargeDipolepert)[__]:>0}
