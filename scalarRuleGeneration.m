(* ::Package:: *)

(* ::Subsubsection:: *)
(*Semi-automated Rule generation*)


InnerEoMOrder[]


FindEoMOrder[IntNull[inside_]]:=InnerEoMOrder[inside];
FindEoMOrder[IntNull[inside_]*TimesExpr_]:=InnerEoMOrder[inside];
FindEoMOrder[PD[{0,-Fra}][IntNull[inside_]]*TimesExpr_]:=.0001+InnerEoMOrder[inside];
FindEoMOrder[PD[{0,-Fra}][PD[{0,-Fra}][IntNull[inside_]]]*TimesExpr_]:=.0002+InnerEoMOrder[inside];
FindEoMOrder[PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][IntNull[inside_]]]]*TimesExpr_]:=.0003+InnerEoMOrder[inside];
FindEoMOrder[PD[{0,-Fra}][IntNull[inside_]]]:=.0001+InnerEoMOrder[inside];
FindEoMOrder[PD[{0,-Fra}][PD[{0,-Fra}][IntNull[inside_]]]]:=.0002+InnerEoMOrder[inside];
FindEoMOrder[PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][IntNull[inside_]]]]]:=.0003+InnerEoMOrder[inside];
FindEoMOrder[expr_]:=0;


InnerEoMOrder[Ns[inds2__] expr_]:=Length[{inds2}];
InnerEoMOrder[Ns[inds2__]]:=Length[{inds2}];


(* ::Text:: *)
(*An alternative heuristic - designed to move things as close as possible to being expressed entirely in body parameters. (prioritizes the expression least like a multipole.) - when in doubt, eliminate to fewer Ns and more r[]'s*)


InnerEoMOrder[(SE|SourceDens)[inds__] r[]^nn_ Ns[inds2__] expr_]:=100+Abs[Length[{inds2}]-nn] + .01*Length[{inds2}];
InnerEoMOrder[(SE|SourceDens)[inds__] r[]^nn_ Ns[inds2__]]      :=100+Abs[Length[{inds2}]-nn]+ .01*Length[{inds2}];
InnerEoMOrder[(SE|SourceDens)[inds__] r[] Ns[inds2__] expr_]    :=100+Abs[Length[{inds2}]-1]+ .01*Length[{inds2}];
InnerEoMOrder[(SE|SourceDens)[inds__] r[] Ns[inds2__]]          :=100+Abs[Length[{inds2}]-1]+ .01*Length[{inds2}];


InnerEoMOrder[(SE|SourceDens)[inds__] r[]^nn_ expr_]:=100+nn;
InnerEoMOrder[(SE|SourceDens)[inds__] r[]^nn_ ]     :=100+nn;
InnerEoMOrder[(SE|SourceDens)[inds__] r[] expr_]    :=100+1;
InnerEoMOrder[(SE|SourceDens)[inds__] r[] ]         :=100+1;


InnerEoMOrder[(SE|SourceDens)[inds__] Ns[inds2__] expr_]:=100+Length[{inds2}]+ .01*Length[{inds2}];
InnerEoMOrder[(SE|SourceDens)[inds__] Ns[inds2__]]      :=100+Length[{inds2}]+ .01*Length[{inds2}];


InnerEoMOrder[(SE|SourceDens)[inds__] expr_]:=100;
InnerEoMOrder[(SE|SourceDens)[inds__]]      :=100;


InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] r[]^nn_ Ns[inds2__] expr_]:=(o+1)*100+Abs[Length[{inds2}]-nn] + .01*Length[{inds2}];
InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] r[]^nn_ Ns[inds2__]]      :=(o+1)*100+Abs[Length[{inds2}]-nn]+ .01*Length[{inds2}];
InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] r[] Ns[inds2__] expr_]    :=(o+1)*100+Abs[Length[{inds2}]-1]+ .01*Length[{inds2}];
InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] r[] Ns[inds2__]]          :=(o+1)*100+Abs[Length[{inds2}]-1]+ .01*Length[{inds2}];


InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] r[]^nn_ expr_]:=(o+1)*100+nn;
InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] r[]^nn_ ]     :=(o+1)*100+nn;
InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] r[] expr_]    :=(o+1)*100+1;
InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] r[] ]         :=(o+1)*100+1;


InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] Ns[inds2__] expr_]:=(o+1)*100+Length[{inds2}]+ .01*Length[{inds2}];
InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] Ns[inds2__]]      :=(o+1)*100+Length[{inds2}]+ .01*Length[{inds2}];


InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__] expr_]:=(o+1)*100;
InnerEoMOrder[(SEpert|SourceDenspert)[LI[o_],inds__]]      :=(o+1)*100;


InnerEoMOrder[expr_]:=0;


GetNumericCoeff[ex_?NumericQ expr_]:=ex;
GetNumericCoeff[expr_]:=1;


IndicesOfCDeltas[ex_ CDelta[rank1_,rank2_][inds__]]:=IndicesOfCDeltas[ex]~Join~{inds};
IndicesOfCDeltas[ex_]:={};


OtherIndexOfCDelta[expr_ CDelta[rank1_,rank2_][ind1_,ind2_],ind2_]:=ind1;
OtherIndexOfCDelta[expr_ CDelta[rank1_,rank2_][ind1_,ind2_],ind1_]:=ind2;


(* ::Text:: *)
(*Removed routines regarding unprocessed expressions*)


SymmetryEquivalentsOfTensor=xAct`xTensor`Private`SymmetryEquivalentsOfTensor;


MakeSymmetrizedSet[expr_]:=Module[{symTensors,replacementRHS,resultString},
							symTensors=Cases[FindAllOfType[expr,Tensor],
								tensor_/;(SymmetryGroupOfTensor[tensor]=!=StrongGenSet[{},GenSet[]])];
							replacementRHS=Alternatives@@(SymmetryEquivalentsOfTensor[#])&/@symTensors;
							resultString=StringReplace[ToString[InputForm[expr]],(ToString[InputForm[symTensors[[#]]]]->"("<>ToString[InputForm[replacementRHS[[#]]]]<>")")&/@Range[Length[symTensors]]];
							Return[ToExpression[resultString]]];


ToPatternInds[exp_List]:=ToPatternInds/@exp;
ToPatternInds[a_?BasisQ]:=a;
ToPatternInds[a_]:=ToExpression[ToString[a]<>"_"];


StripBasis[{a_,b_?BasisQ}]:=a;
StripBasis[exp_List]:=StripBasis/@exp;


GenerateSumRulesFromEoM[expr_,OptionsPattern[]]:=
Module[{rawlhs,rawrhs,firstlhs,truelhs,lhsDeltaIndices,NewDeltaIndices1,NewDeltaIndices2,singleMaxPos,
		NewIndexList,NewCDeltas,IndexSigns,symmComb=False,FreeIndices,IndicesList,FreePatternIndicesList,
		EoMOrderList=FindEoMOrder/@(List@@expr),maxPos},
	If[Head@expr===Plus,
		maxPos=Position[EoMOrderList,Max[EoMOrderList]];
		If[Length[maxPos]>1, (*If the 'best lhs' term is degenerate, we have a Sum rule to generate*)
			firstlhs=First@((expr)[[#]]&/@maxPos);
			rawlhs=((expr)[[#]]&/@maxPos);
			rawrhs=Plus@@Delete[(List@@expr),maxPos];
			rawrhs=(-1*rawrhs/GetNumericCoeff[firstlhs])//Expand//GenerateNewDummies;
			rawlhs=rawlhs/GetNumericCoeff[firstlhs]//Expand;
			IndicesList=DeleteDuplicates[Join@@IndicesOf[Free]/@List@@(rawlhs)/.IndexList->List];
			IndicesList=StripBasis[IndicesList];
			FreePatternIndicesList=ToPatternInds[IndicesList];
			(*For each symmetric tensor in lhs we need either a separate rule or a _separate pattern entry_*)
			truelhs=MakeSymmetrizedSet/@(GeneratePatternDummies/@rawlhs);
			(*Print[{truelhs,"Goes to",rawrhs}];*)
			Return[{(ToExpression["{"<>ToString[InputForm[truelhs]]<>",{"<>
										ToString[FreePatternIndicesList]<>","<>ToString[IndicesList]<>"},"<>ToString[InputForm[rawrhs]]<>"}"])}];
		,
			Return[{}];
		];
	,
		Return[{}];
	];
	Return[{}];
];


NZSumEoMRules[1]={};


GenerateRulesFromEoM[expr_,OptionsPattern[]]:=
Module[{rawlhs,rawrhs,firstlhs,truelhs,lhsDeltaIndices,NewDeltaIndices1,NewDeltaIndices2,singleMaxPos,
		NewIndexList,NewCDeltas,IndexSigns,symmComb=False,FreeIndices,IndicesList,FreePatternIndicesList,
		EoMOrderList=FindEoMOrder/@(List@@expr),maxPos},
	If[Head@expr===Plus,
		maxPos=Position[EoMOrderList,Max[EoMOrderList]];
		If[Length[maxPos]>1, (*If the 'best lhs' term is degenerate, we have a Sum rule to generate*)
			Return[{}]
		,
			singleMaxPos=First@(First@maxPos);
			rawlhs=expr[[singleMaxPos]];
			rawrhs=Delete[expr,singleMaxPos];
		];
	,
		rawlhs=expr;
		rawrhs=0;
		If[rawlhs===0,Return[{}];];
	];
	rawrhs=(-1*rawrhs/GetNumericCoeff[rawlhs])//Expand;
	rawlhs=rawlhs/GetNumericCoeff[rawlhs]//Expand;
	lhsDeltaIndices=Intersection[(IndicesOf[Free][rawlhs]/.IndexList->List),IndicesOfCDeltas[rawlhs]];
	NewDeltaIndices1=Expand[-1*lhsDeltaIndices];
	NewDeltaIndices2=({Unique[#[[1]]],#[[2]]}&/@(UpIndex/@(OtherIndexOfCDelta[rawlhs,#]&/@lhsDeltaIndices)))*(-1*(BoolToSign/@(UpIndexQ/@(OtherIndexOfCDelta[rawlhs,#]&/@lhsDeltaIndices))));
	NewIndexList={NewDeltaIndices1[[#]],NewDeltaIndices2[[#]]}&/@Range[Length[NewDeltaIndices2]];
	NewCDeltas = CDelta[#[[1]][[2]],#[[2]][[2]]][Sequence@@#]&/@NewIndexList;
	rawlhs=Times[rawlhs,Sequence@@NewCDeltas]//ExpandAll;
	rawrhs=Times[rawrhs,Sequence@@NewCDeltas]//ExpandAll;
	With[{lhs=rawlhs,rhs=(rawrhs//GenerateNewDummies),dlhs=PD[-{0,Ret}][rawlhs]},
		If[OptionValue[Verbose],
			Print[rhs];
			Print[lhs];
		];
		Return[MakeRule[{lhs,rhs},MetricOn->None]];
	];
];Options[GenerateRulesFromEoM]={Verbose->False};
