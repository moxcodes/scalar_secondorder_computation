(* ::Package:: *)

ClearAll[ExtractMatch];


SetAttributes[ExtractMatch,HoldFirst];


ExtractMatch[list_,val_]:=Module[{},list=Append[ReleaseHold[list],val];Return[True];];


CanonicalEqual[a_,b_]:=(ToCanonical[a,UseMetricOnVBundle->None]==ToCanonical[b,UseMetricOnVBundle->None]);


RecursiveSumMatch[__][expr_]/;!(Head[expr]===Plus)={};


RecursiveSumMatch[remainingTerms_,matchIndSet_,indSet_,coeffSet_,posList_][expr_Plus]:=
Module[{opTerm,ii,isMatched,tempIndexSet,tempCoeffSet,tempIndexString,tempCoeffString,recursePosList,newSet},
If[Length[remainingTerms]==0,Return[{posList,coeffSet[[1]],indSet[[1]]}];];
If[Length[indSet]>0 && Length[indSet[[1]]]==Length[matchIndSet[[1]]],
	opTerm=(remainingTerms[[1]]/.(Join@@({matchIndSet[[2]][[#]]->indSet[[1]][[#]]}&/@Range[Length[indSet[[1]]]])));,
	opTerm=(remainingTerms[[1]]/.(Join@@({matchIndSet[[2]][[#]]:>matchIndSet[[1]][[#]]}&/@Range[Length[matchIndSet[[1]]]])));];
For[ii=1,ii<=Length[expr],ii++,
	tempCoeffSet=coeffSet;
	tempIndexSet=indSet;
	If[!MemberQ[posList,ii],
		If[Length[indSet]>0 && Length[indSet[[1]]]==Length[matchIndSet[[1]]],
			Switch[coeffSet[[1]]
				,1,
				isMatched=MatchQ[expr[[ii]],opTerm];
				tempCoeffSet=Append[tempCoeffSet,1];
				,-1,
				isMatched=(MatchQ[expr[[ii]],-1*opTerm]);
				tempCoeffSet=Append[tempCoeffSet,-1];
				,_,
				isMatched=(MatchQ[expr[[ii]],arb_*opTerm/;ExtractMatch[tempCoeffSet,arb]]
								&&CanonicalEqual[tempCoeffSet[[Length[tempCoeffSet]]],tempCoeffSet[[Length[tempCoeffSet]-1]]]);
				If[!isMatched,
					tempCoeffSet=coeffSet;
	                isMatched=(MatchQ[expr[[ii]],arb_*(-1*opTerm)/;ExtractMatch[tempCoeffSet,-arb]]
								&&CanonicalEqual[tempCoeffSet[[Length[tempCoeffSet]]],tempCoeffSet[[Length[tempCoeffSet]-1]]]);
				];
			];
		,
			newSet=matchIndSet[[2]];
			tempIndexString=StringTake[ToString[Hold[tempIndexSet]],{6,-2}];
			isMatched=ToExpression["MatchQ["<>ToString[InputForm[expr[[ii]]]]<>","<>ToString[opTerm]<>"/;ExtractMatch["
							<>tempIndexString<>","<>ToString[newSet]<>"]]"];
			If[isMatched,
				tempCoeffSet={1};
			,
				isMatched=ToExpression["MatchQ["<>ToString[InputForm[expr[[ii]]]]<>","<>ToString[-1*opTerm]<>"/;ExtractMatch["
							<>tempIndexString<>","<>ToString[newSet]<>"]]"];
			If[isMatched,
				tempCoeffSet={-1};
			,	
				tempCoeffString=StringTake[ToString[Hold[tempCoeffSet]],{6,-2}];
				isMatched=ToExpression["MatchQ["<>ToString[InputForm[expr[[ii]]]]<>",arb_*"<>ToString[opTerm]<>"/;ExtractMatch["
							<>tempIndexString<>","<>ToString[newSet]<>"]&&ExtractMatch["<>tempCoeffString<>",arb]]"];
			If[!isMatched,
				isMatched=ToExpression["MatchQ["<>ToString[InputForm[expr[[ii]]]]<>",arb_*"<>ToString[-opTerm]<>"/;ExtractMatch["
							<>tempIndexString<>","<>ToString[newSet]<>"]&&ExtractMatch["<>tempCoeffString<>",-1*arb]]"];
			];];];
		];
		If[isMatched, (* We found a match! recurse....*)
			recursePosList = RecursiveSumMatch[Delete[remainingTerms,1],matchIndSet,tempIndexSet,tempCoeffSet,{ii}~Join~posList][expr];
			If[Length[recursePosList]>0 && Length[recursePosList[[1]]] == Length[posList]+Length[remainingTerms],
				Return[recursePosList];,
				Return[{}];
			];
		];
	];
];Return[{}];];


ApplySumRule[__][expr_]/;!(Head[expr]===Plus):=expr;


ApplySumRule[lhs_,freeInds_,rhs_][expr_Plus]:=
Module[{matchSet,newExpr=expr},
	matchSet=RecursiveSumMatch[lhs,freeInds,{},{},{}][newExpr];
	While[!(matchSet==={}),
	newExpr=(Delete[newExpr,(List/@matchSet[[1]])] 
			+ (matchSet[[2]]//GenerateNewDummies)*
					(rhs/.(Join@@({freeInds[[2]][[#]]->matchSet[[3]][[#]]}&/@Range[Length[freeInds[[2]]]]))));
	newExpr=newExpr//ToCanonical[#,UseMetricOnVBundle->None]&;
	matchSet=RecursiveSumMatch[lhs,freeInds,{},{},{}][newExpr];
	];
	Return[newExpr];
];


ApplySumRuleList[SumRuleList_][expr_]:=
Module[{newExpr=expr,ii},
	For[ii=1,ii<=Length[SumRuleList],ii++,
		newExpr=ApplySumRule[Sequence@@SumRuleList[[ii]]][newExpr];
	];
	Return[newExpr];
];
