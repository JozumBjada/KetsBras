(* ::Package:: *)

(* ::Title:: *)
(*Introduction*)


(* ::Subsubsection:: *)
(*Introduction*)


BeginPackage["KetsBras`"];


(*created in version "11.0.1 for Linux x86 (64-bit) (September 21, 2016)"*)


(* ::Subsubsection:: *)
(*Declaration of All Suitable Symbols in Public Context*)


`Private`listOfSymbols={
	idket,partTr,partTrSymb,partTrInt,toKet,fromKet,toKetBra,fromKetBra,linearCombinationQ,
	replaceKet,factorKetsList,kroneckerKetProducts,getSpecs,infiniteBasis,generateKets,getSpecs,
	onBases,addBasis,clearBasis,identifyBases,basisVectorQ,basisQ,Ket,Bra,Tr,Normalize,Norm,changeBasis,
	AngleBracket,HoldForm@$evaluateBasisProduct,infiniteBasisQ,addBasisTransformation,getInfiniteLabel,
	HoldForm@$onBasesTransformations,clearBasisTransformation,checkBasisTr,permuteKets,unfactorKetsList};


(* ::Subsubsection::Closed:: *)
(*Predefined Kets*)


{k0,k1}={Ket[0],Ket[1]};

(*kd=Ket[d]=1/Sqrt[2] (Ket[0]+Ket[1]);
ka=Ket[a]=1/Sqrt[2] (Ket[0]-Ket[1]);
kr=Ket[r]=1/Sqrt[2] (Ket[0]+I Ket[1]);
kl=Ket[l]=1/Sqrt[2] (Ket[0]-I Ket[1]);

psip=Ket[SuperPlus[\[CapitalPsi]]]=1/Sqrt[2] (Ket[0,1]+Ket[1,0]);
psim=Ket[SuperMinus[\[CapitalPsi]]]=1/Sqrt[2] (Ket[0,1]-Ket[1,0]);
phip=Ket[SuperPlus[\[CapitalPhi]]]=1/Sqrt[2] (Ket[0,0]+Ket[1,1]);
phim=Ket[SuperMinus[\[CapitalPhi]]]=1/Sqrt[2] (Ket[0,0]-Ket[1,1]);*)

kd=1/Sqrt[2] (Ket[0]+Ket[1]);
ka=1/Sqrt[2] (Ket[0]-Ket[1]);
kr=1/Sqrt[2] (Ket[0]+I Ket[1]);
kl=1/Sqrt[2] (Ket[0]-I Ket[1]);

psip=1/Sqrt[2] (Ket[0,1]+Ket[1,0]);
psim=1/Sqrt[2] (Ket[0,1]-Ket[1,0]);
phip=1/Sqrt[2] (Ket[0,0]+Ket[1,1]);
phim=1/Sqrt[2] (Ket[0,0]-Ket[1,1]);


(* ::Subsubsection::Closed:: *)
(*Start of Private Context*)


Begin["`Private`"];


(* ::Subsubsection::Closed:: *)
(*Auxiliary Routines for Documentation Strings Customization*)


matchingBrackets[str_]:=StringCount[str,"["]==StringCount[str,"]"]
emphDocRule = WordBoundary ~~ "emph[" ~~ Shortest[x___] ~~ "]"/;matchingBrackets[x] :> ToString[Style[ToExpression[x, StandardForm, Defer], Italic], TraditionalForm];
createDocRules[listOfSymbolNames_] := (str : (WordBoundary ~~ # ~~ "[" ~~ Shortest[x___] ~~ "]")/;matchingBrackets[x] :> ToString[Style[ToExpression[str, StandardForm, Defer], Italic], TraditionalForm]) & /@ listOfSymbolNames


toNiceForm::usage="This routine is meant to format documentation strings of other routines and symbols. Symbols given in a list listOfSymbolNames are replaced in strToModify by their formatted versions. Two auxiliary 'subroutines' are used: emphDocRule (rule that every occurence of 'emph[x___]' replaces with italicized x) and createDocRules (based on given symbol names (in FullForm) creates substitution list where each occurence of given symbol name is replaced with TraditionalForm of the same symbol).";


toNiceForm[strToModify_, listOfSymbolNames_] := StringReplace[strToModify, Join[createDocRules[listOfSymbolNames], {emphDocRule}]]
toNiceFormBraKet[strToModify_]:=toNiceForm[strToModify,{"Bra","Ket"}]


(* ::Subsubsection::Closed:: *)
(*Get specification of Kets etc.*)


getSpecs::usage=toNiceFormBraKet@"getSpecs[emph[expr]_]: Provided emph[expr] is of the form head[\!\(\*SubscriptBox[\(a\), \(1\)]\), ..., \!\(\*SubscriptBox[\(a\), \(n\)]\)], where emph[n]>=1 and emph[head] has attribute HoldAll, return list of strings given by SymbolName when called on each of the arguments.";


getSpecs[expr_]:=List@@(Function[{$$x},If[!MatchQ[Unevaluated[$$x],_Symbol],ToString[$$x],SymbolName[Unevaluated[$$x]]],HoldAll]/@expr)
(*this complicated arcane form of the function is used because then arguments of expr are not evaluated*)


(* ::Title::Closed:: *)
(*Bases*)


(* ::Subsubsection::Closed:: *)
(*Token idket*)


idket::usage=toNiceFormBraKet@"Special symbol that is handy in calculation of e.g. partial trace. Construct Ket[a, idket, b], that can be input as Ket[a]**Ket[idket]**Ket[b], represents expression Ket[a]\[TensorProduct]\[DoubleStruckCapitalI]\[TensorProduct]Ket[b], where \[DoubleStruckCapitalI] is an identity. As a consequence, Bra[idket]**Ket[a]==Ket[a] for any (integral) emph[a]; similarly for Bras. For each dimension individual emph[idket] must be specified, i.e. identity in two-dimensional subspace must be entered as Ket[idket, idket] etc. Scalar product \[LeftAngleBracket]{emph[idket]},{emph[idket]}\[RightAngleBracket] is not evaluated.";


Protect[idket];


(* ::Subsubsection::Closed:: *)
(*$onBases*)


$onBases=<|"Integral"->infiniteBasis[None],"IdentityKet"->{Ket[idket]}|>;


(* ::Subsubsection::Closed:: *)
(*$onBasesTransformations*)


$onBasesTransformations=<||>;


(* ::Subsubsection::Closed:: *)
(*onBases*)


onBases::usage=toNiceFormBraKet@"onBases[emph[name]_:All]: Show elements of orthonormal basis emph[name]; if emph[name] is All or omitted, list all defined bases except for default integer basis.";


(*SyntaxInformation[onBases]={"ArgumentsPattern"\[Rule]{_}};*)


SetAttributes[infiniteBasis,HoldAll];


onBases[name_:All]:=$onBases[[name]]


(* ::Subsubsection::Closed:: *)
(*basisQ*)


basisQ::usage=toNiceFormBraKet@"basisQ[emph[bas]_]: If emph[bas] is a valid basis, returns True, otherwise returns False. Valid basis is either a user basis added by addBasis or 'Integral' that stands for integral basis.";


SyntaxInformation[basisQ]={"ArgumentsPattern"->{_}};


basisQ[bas_String]:=!MissingQ[onBases[bas]]


(* ::Subsubsection::Closed:: *)
(*infiniteBasisQ*)


infiniteBasisQ::usage=toNiceFormBraKet@"infiniteBasisQ[emph[bas]_]: If emph[bas] is a valid infinite basis, returns True, otherwise returns False. Valid basis is either a user basis added by addBasis or 'Integral' that stands for integral basis.";


SyntaxInformation[infiniteBasisQ]={"ArgumentsPattern"->{_}};


infiniteBasisQ[bas_String]:=basisQ[bas]&&Head[onBases[bas]]===infiniteBasis


(* ::Subsubsection::Closed:: *)
(*getInfiniteLabel*)


getInfiniteLabel::usage=toNiceFormBraKet@"getInfiniteLabel[emph[infbas]_String]: For infinite basis emph[infbas] defined as infiniteBasis[emph[lab]], returns emph[lab] and flag, whether emph[lab] is a String or a Symbol. Specifically, {emph[lab],False} is returned when emph[lab] is a String, and {ToString[emph[lab]],True} when emph[lab] is a Symbol. For finite bases {$Failed,False} is returned.";


SyntaxInformation[getInfiniteLabel]={"ArgumentsPattern"->{_}};


getInfiniteLabel[infbas_String]:=Module[{bas},
	If[infiniteBasisQ[infbas],
		bas=onBases[infbas];
		{First@getSpecs[bas],MatchQ[bas,infiniteBasis[_Symbol]]}
		,
		{$Failed,False}
	]
]


(* ::Subsubsection::Closed:: *)
(*basisVectorQ*)


basisVectorQ::usage=toNiceFormBraKet@"basisVectorQ[emph[bas]_,emph[vec]_]: If emph[vec] is a specification of a vector that forms basis emph[bas], returns True, otherwise returns False. Argument emph[vec] can be either of the form Ket[spec] or just emph[spec]. Token emph[idket] is understood as a basis vector of basis 'IdentityKet'.
\nbasisVectorQ[emph[bas]_] is an operator version that can be used as basisVectorQ[emph[bas]][emph[vec]_].";


SyntaxInformation[basisVectorQ]={"ArgumentsPattern"->{__}};


SetAttributes[basisVectorQ,HoldRest]


basisVectorQ::multbas="Specification corresponds to multiple subspaces. Please provide unipartite specification.";


basisVectorQ[bas_,idket|Ket[idket]|Bra[idket]]:=bas==="IdentityKet"
basisVectorQ[bas_,vec_Bra]:=basisVectorQ[bas,Evaluate[vec\[ConjugateTranspose]]]
basisVectorQ[bas_,vec_Ket]:=Module[{bascontent=onBases[bas],prefix,prefixsymb,vecsymb},
	If[Length[vec]>1,Message[basisVectorQ::multbas];Return[False]];	
	If[bas==="Integral",
		Return[MatchQ[vec,Ket[_Integer]]];
	];
		
	If[MatchQ[bascontent,_infiniteBasis],
		prefix=First@getSpecs[bascontent];
		prefixsymb=MatchQ[bascontent,infiniteBasis[_Symbol]];
		vecsymb=MatchQ[vec,Ket[_Symbol]];
		If[vecsymb=!=prefixsymb,Return[False]];		
		StringMatchQ[First@getSpecs[vec],prefix~~(DigitCharacter..)]
		,
		MemberQ[bascontent,vec]
	]
]
basisVectorQ[bas_,vec_]:=basisVectorQ[bas,Ket[vec]]
basisVectorQ[bas_String]:=basisVectorQ[bas]=Function[{$$vec},basisVectorQ[bas,Unevaluated[$$vec]],HoldAll]


(* ::Subsubsection::Closed:: *)
(*identifyBases*)


identifyBases::usage=toNiceFormBraKet@"identifyBases[emph[listvec]_]: Returns names of defined bases that contain individual vectors in emph[listvec]. If no such basis exists, None is returned. Assumes that emph[listvec] is Ket or a list of Kets. Token emph[idket] is understood as a basis vector of basis 'IdentityKet'. If Kets in emph[listvec] are multipartite with the same number of subspaces each, then the output of this function is a list whose emph[i]-th element says to which basis Kets of emph[i]-th subspace (for all multipartite Kets) belong.";


SyntaxInformation[identifyBases]={"ArgumentsPattern"->{_}};


identifyBases::invinp="Some of input arguments are not Kets or elementary vectors.";
identifyBases::difflen="Kets do not have the same number of subspaces. These numbers of subspaces were found: ``.";
identifyBases::notuniq="For some subspaces there are vectors from multiple bases.";


SetAttributes[identifyBases,HoldAll]


identifyBases[listvec_Ket,rest___]:=identifyBases[{listvec},rest]


identifyBases[listvec_List,checkuniq_:True]:=
	Module[{loclist=listvec,keys=Keys[onBases[]],memb,names,lengths},
		If[Not@AllTrue[loclist,MatchQ[_Ket]],
			Message[identifyBases::invinp];Return[]];

		(*from multipartite Kets make lists of unipartite Kets*)
		loclist=List@@ReleaseHold@Map[Ket,Hold[#],{2}]&/@loclist;

		lengths=Union[Length/@loclist];
		If[Length[lengths]>1,Message[identifyBases::difflen,lengths];Return[]];

		(*for each list of unipartite kets find out which basis it belongs to*)
		memb=Table[Map[basisVectorQ[bas],loclist,{2}],{bas,keys}];
		
		(*let each row in memb correspond to one vector in listvec, each column then
		corresponds to each of unipartite Kets and the last dimension specifies which
		basis given unipartite Ket belongs to*)
		memb=TensorTranspose[memb,{3,1,2}];
		names=Map[First[Pick[keys,#],None]&,memb,{2}];
		names=Union/@Transpose[names];
		
		If[checkuniq,
			If[AnyTrue[names,Length[#]>1&],Message[identifyBases::notuniq];Return[]];
			names=Flatten[names];	
		];
		names
	]


(* ::Subsubsection::Closed:: *)
(*clearBasis*)


clearBasis::usage=toNiceFormBraKet@"clearBasis[emph[name]_]: Remove basis with name emph[name] from the list of bases.";


SyntaxInformation[clearBasis]={"ArgumentsPattern"->{_}};


clearBasis[name_]:=$onBases[name]=.


(* ::Subsubsection::Closed:: *)
(*addBasis*)


addBasis::usage=toNiceFormBraKet@"addBasis[emph[name]_,emph[basis]_]: Add basis with name emph[name] to the list of bases.";


SyntaxInformation[addBasis]={"ArgumentsPattern"->{_,_}};


addBasis::invname="Name '``' already used.";
addBasis::invbas="Input basis is not a list of Kets with unipartite system specification or infiniteBasis construct with a single argument.";
addBasis::dupl="Input basis contains duplicates.";
addBasis::intval="Vector specifications cannot be integers.";
addBasis::intbas="Infinite basis specification must be a symbol or a string.";
addBasis::twin="Some Ket specifications are already used in another basis.";
addBasis::infspec="Infinite basis '``' already used.";


addBasis[name_String,basis_]:=
	Module[{infbas},
		If[MemberQ[Keys[$onBases],name],
			Message[addBasis::invname,name];Return[]];
		
		Which[
			MatchQ[basis,{Ket[_]..}],
				If[AnyTrue[basis,MatchQ[Ket[_Integer]]],
					Message[addBasis::intval];Return[]];
				If[!DuplicateFreeQ[basis],
					Message[addBasis::dupl];Return[]];
				If[ContainsAny[basis,Flatten@Values[$onBases]],
					Message[addBasis::twin];Return[]];,
			MatchQ[basis,infiniteBasis[_]],
				infbas=Cases[$onBases,_infiniteBasis];
				If[AnyTrue[infbas,EqualTo[basis]],
					Message[addBasis::infspec,InputForm[basis]];Return[]];
				If[(!MatchQ[basis,infiniteBasis[_Symbol]])&&
					(!MatchQ[basis,infiniteBasis[_String]]),
					Message[addBasis::intbas];Return[]];,
			True,
				Message[addBasis::invbas];Return[];
		];
	
		AppendTo[$onBases,name->basis];
	]


(* ::Subsubsection::Closed:: *)
(*addBasisTransformation*)


addBasisTransformation::usage=toNiceFormBraKet@"addBasisTransformation[emph[frombasis]_String,emph[tobasis]_String,mat]: Add a matrix emph[mat] specifying how basis vectors from basis emph[frombasis] relate to vectors in emph[tobasis]. Infinite bases are not supported.";


SyntaxInformation[addBasisTransformation]={"ArgumentsPattern"->{__}};


addBasisTransformation::nonunit="Specified transition matrix is not (explicitly) unitary. Only orthonormal bases are allowed.";
addBasisTransformation::infbas="Infinite bases are not supported.";
addBasisTransformation::uneq="Specified bases have different number of basis vectors.";
addBasisTransformation::exists="Specified bases already have the transition matrix set. It is rewritten.";


addBasisTransformation[frombasis_String,tobasis_String,mat_?MatrixQ]:=Module[{bothkeys,transitions,totrans,fromtrans},
	If[MemberQ[Keys[$onBasesTransformations],{frombasis,tobasis}],
		Message[addBasisTransformation::exists];];

	If[infiniteBasisQ[frombasis]||infiniteBasisQ[tobasis],
		Message[addBasisTransformation::infbas];Return[]];
	If[Length[onBases[frombasis]]!=Length[onBases[tobasis]],
		Message[addBasisTransformation::uneq];Return[]];
	If[Not@UnitaryMatrixQ[mat],
		Message[addBasisTransformation::nonunit];Return[]];
		
	(*add transition and its inverse*)
	bothkeys[f_,t_,m_]:={{f,t}->m,{t,f}->m\[ConjugateTranspose]};
	AssociateTo[$onBasesTransformations,bothkeys[frombasis,tobasis,mat]];
	
	(*add/update all other mutual transitions for newly created links between bases*)
	transitions=Keys[$onBasesTransformations];
	fromtrans=Cases[transitions,{frombasis,b_}:>b]/.tobasis->Nothing;
	totrans=Cases[transitions,{tobasis,b_}:>b]/.frombasis->Nothing;
	
	transitions=bothkeys[#,tobasis,mat . $onBasesTransformations[{#,frombasis}]]&/@fromtrans;
	AssociateTo[$onBasesTransformations,Flatten@transitions];
	
	transitions=bothkeys[frombasis,#,$onBasesTransformations[{tobasis,#}] . mat]&/@totrans;
	AssociateTo[$onBasesTransformations,Flatten@transitions];
]


(* ::Subsubsection::Closed:: *)
(*clearBasisTransformation*)


clearBasisTransformation::usage=toNiceFormBraKet@"clearBasisTransformation[emph[basis]_String]: For given basis emph[basis] remove all transformation matrices that connect this basis to other bases. Unlike addBasisTransformation, here only one basis is specified.";


SyntaxInformation[clearBasisTransformation]={"ArgumentsPattern"->{_}};


clearBasisTransformation[basis_]:=Module[{keys},

	(*remove all transformation matrices that have something to do with the given basis*)
	keys=Cases[Keys[$onBasesTransformations],{basis,_}|{_,basis}];
	KeyDropFrom[$onBasesTransformations,keys];
]


(* ::Subsubsection::Closed:: *)
(*generateKets*)


generateKets::usage=toNiceFormBraKet@"generateKets[emph[basis]_infiniteBasis,emph[specs]_List]: Given infinite basis emph[basis] and a list of number specifications emph[specs], return a list of Kets from emph[basis] with these specifications. As emph[basis] one can also specify name of a predefined infinite basis.
generateKets[emph[basis]_,emph[num]_Integer]: Specification is given as {1, ..., num}.";


SyntaxInformation[generateKets]={"ArgumentsPattern"->{_,_}};


generateKets::invbas="Invalid basis '``'.";
generateKets::invnum="Invalid number `` of Kets to be generated.";
generateKets::invspecs="Specification `` is not a list of integers.";
generateKets::nonpos="For non-integral infinite bases only positive specifications are allowed.";


generateKets[basis_String,rest___]:=Module[{bas=onBases[basis]},
	If[MatchQ[bas,_Missing]||!MatchQ[bas,_infiniteBasis],
		Message[generateKets::invbas,basis];Return[]];
	generateKets[bas,rest]
]
generateKets[basis_infiniteBasis,num_Integer]:=Module[{specs},
	If[NonPositive[num],Message[generateKets::invnum,num];Return[]];
	specs=Range[num];
	generateKets[basis,specs]
]
generateKets[basis_infiniteBasis,specs_List]:=Module[{prefix,strings,kets,bas=basis},
	If[!MatchQ[specs,{__Integer}],Message[generateKets::invspecs,specs];Return[]];
	
	If[bas===infiniteBasis[None],
		Return[Ket/@specs];];
	
	If[AnyTrue[specs,NonPositive],
		Message[generateKets::nonpos];Return[]];
	
	prefix=First@getSpecs[bas];
	strings=prefix<>ToString[#]&/@specs;
	If[MatchQ[bas,infiniteBasis[_Symbol]],
		kets=ToExpression[#,StandardForm,Ket]&/@strings;,
		kets=Ket/@strings;
	];
	kets
]


(* ::Title::Closed:: *)
(*Scalar Product*)


(* ::Subsubsection::Closed:: *)
(*$evaluateBasisProduct*)


$evaluateBasisProduct::usage="If True, then scalar products \!\(\*TemplateBox[{SubscriptBox[\"a\", \"i\"]},\n\"Bra\"]\)\!\(\*TemplateBox[{SubscriptBox[\"b\", \"j\"]},\n\"Ket\"]\) of basis vectors from two different bases are evaluated (if transformation between them is specified), otherwise the ketbra is left unevaluated.";


Set::braket="$evaluateBasisProduct can be set either to True or to False.";


$evaluateBasisProduct/:Set[$evaluateBasisProduct,rhs_]:=
	If[!MatchQ[rhs,True|False],Message[Set::braket];$evaluateBasisProduct,rhs]


$evaluateBasisProduct=False;


(* ::Subsubsection::Closed:: *)
(*BraKets implemented with help of AngleBracket*)


AngleBracket::usage="AngleBracket[{a1,a2,a3,...},{b1,b2,b3,b...}] stands for a scalar product \[LeftAngleBracket]a1,a2,a3,...|b1,b2,b3,...\[RightAngleBracket]. If all ai's and bi's are Integers or idket tokens, the expression is evaluated. Number of ai's and number of bi's do not have to be equal. In that case the trailing missing Kets or Bras are effectively understood as Ket[idket]'s or Bra[idket]'s, respectively.";


SyntaxInformation[AngleBracket]={"ArgumentsPattern"->{_,_}};


SetAttributes[AngleBracket,HoldAll];


AngleBracket::incomp="Value of the scalar product contains both Kets and Bras.";


(*a scalar product of basis vectors; other vectors have to be specified in terms of basis
vectors in order for their scalar product to be evaluated*)


AngleBracket[{a__},{b__}] /; ValueQ[Bra[a]] || ValueQ[Ket[b]] := 
	CircleTimes@@(Bra/@Unevaluated[{a}]) ** CircleTimes@@(Ket/@Unevaluated[{b}])
(*this line here is due to situation when we create a scalar product of as yet undefined kets and
bras; if we define these afterwards we expect the already created scalar product to update accordingly during reevaluation;
without this line this feature would not work*)


AngleBracket[{idket},{b_?(#=!=idket&)}]:=Ket[b]
AngleBracket[{a_?(#=!=idket&)},{idket}]:=Bra[a]


(*Integral basis is easy to define scalar products for*)
AngleBracket[{a___Integer},{b___Integer}]/;Length[{a}]==Length[{b}]:=Boole[{a}=={b}]


(*Let's hope, that bra and ket are already irreducible in a sense that
there are no linear combinations assigned to them; this condition is hopefully implemented by
rules above*)
AngleBracket[{bra__},{ket__}]/;Length[{bra}]==Length[{ket}]>1:=Module[
	{bralist=Bra/@Unevaluated[{bra}],ketlist=Ket/@Unevaluated[{ket}],pairs,aux},
	
	pairs=Transpose[{bralist,ketlist}];
	pairs=evaluateScalarProduct@@@pairs;
	Times@@pairs
	(*pairs=CircleTimes@@Join[pairs,{Ket[aux]}];
	pairs*)
	(*If[FreeQ[pairs,_Ket|_Bra],pairs/.CircleTimes\[Rule]Times,pairs]*)
]


(*AngleBracket[{bra_},{ket_}]/;First[evaluateableScalProd[Bra[bra],Ket[ket]]]:=Boole[Bra[bra]\[ConjugateTranspose]===Ket[ket]]*)


AngleBracket[{bra_},{ket_}]:=Module[{cond=evaluateableScalProd[Bra[bra],Ket[ket]]},
	(AngleBracket[{bra},{ket}]=evaluateScalarProduct[Bra[bra],Ket[ket],cond])/;First[cond]
]


evaluateScalarProduct[bra_Bra,ket_Ket,cond_:None]:=
	evaluateScalarProduct[bra,ket,None]=evaluateScalarProduct[bra,ket,cond]=Module[
	{iseval,brabas,ketbas,isequal,row,col},
	
	{iseval,brabas,ketbas,isequal}=If[cond=!=None,cond,evaluateableScalProd[bra,ket]];
	If[iseval,
		If[isequal,
			Boole[bra\[ConjugateTranspose]===ket]
			,
			row=First@FirstPosition[onBases[ketbas],ket];
			col=First@FirstPosition[onBases[brabas],bra\[ConjugateTranspose]];
			$onBasesTransformations[{brabas,ketbas}][[row,col]]
		]		
		,
		bra**ket
	]
]


evaluateableScalProd[bra_Bra,ket_Ket]:=evaluateableScalProd[bra,ket]=Module[
	{keys=Keys[onBases[]],brabas,ketbas,iseval},
	
	brabas=SelectFirst[keys,basisVectorQ[#,bra]&,None];
	ketbas=SelectFirst[keys,basisVectorQ[#,ket]&,None];
	
	(*evaluate scalar product only when you can identify bases of both bra and ket; if at least
	one of them does not belong to any basis, you cannot know the result; even if bra\[ConjugateTranspose]===ket 
	and ketbas is None, its norm does not have to be unity and therefore bra**ket has to be
	returned*)
	iseval=brabas===ketbas&&ketbas=!=None||Not@MissingQ[$onBasesTransformations[{brabas,ketbas}]];
	{iseval,brabas,ketbas,brabas===ketbas}
]


(* ::Subsubsection::Closed:: *)
(*Norms of Kets and Bras*)


Unprotect[Norm,Normalize];


Norm[expr_]/;linearCombinationQ[expr,_Ket]:=Sqrt[(expr)\[ConjugateTranspose]**expr]
Norm[expr_]/;linearCombinationQ[expr,_Bra]:=Sqrt[expr**(expr)\[ConjugateTranspose]]


Norm[coef_?(FreeQ[#,Ket|Bra]&) expr_]:=Abs[coef]Norm[expr]


Normalize[expr_]/;(linearCombinationQ[expr,_Ket]||linearCombinationQ[expr,_Bra]):=1/Norm[expr] expr


Protect[Norm,Normalize];


(* ::Title::Closed:: *)
(*Kets, Bras*)


(* ::Subsubsection::Closed:: *)
(*Kets, Bras*)


Ket::usage = toNiceFormBraKet["Built-in command Ket is overloaded, so one can use it as usual ket vectors. Also see info for Bra and idket. These rules apply:
 1. Kets Ket[0], Ket[1], Ket[2], etc. are precluded from being assigned any value. These are considered to form an orthonormal basis.
 2. It holds that (Ket[x])\[ConjugateTranspose]==Bra[x], where \[ConjugateTranspose] is a ConjugateTranspose command. This feature works even when Ket[x] is a linear combination of Kets. Analogously for Bras.
 3. When one makes assignment Ket[x] = emph[val] for any valid emph[x] and emph[val], then automatically the system performs assigment Bra[x]=(emph[val])\[ConjugateTranspose]. Analogously for Bras. Assignments are only possible, when Kets (or Bras) do not represent a tensor product, i.e. assignment to e.g. Ket[a,b] throws an error. Moreover, in expression Ket[x] = emph[val], emph[val] must be a linear combination of Kets; similarly for Bras.
 4. Tensor and scalar products are implemented with help of NonCommutativeMultiply. A tensor product of Ket[a] and Ket[b] is input as Ket[a]**Ket[b], which results in creation of a composite ket Ket[a,b]. Analogously for Bras. A scalar product of Bra[a] and Ket[b] is input as Bra[a]**Ket[b]. This sequence is converted into AngleBracket construct that is output as \[LeftAngleBracket]{emph[a]},{emph[b]}\[RightAngleBracket] and, if possible, evaluated. For details see the next bullet. KetBras, and their relation to Kets and Bras, are automatically implemented by associativity behavior of NonCommutativeMultiply. Moreover, Ket[]**Ket[x]==Ket[x] and similarly for reversed order and for Bras.
 5. Details of scalar product evaluation. A given scalar product \[LeftAngleBracket]{emph[a]},{emph[b]}\[RightAngleBracket] is evaluated only if emph[a] and emph[b] are sequences composed of integers or emph[idket] tokens. If sequence emph[a] is shorter than sequence emph[b], then the whole scalar product of two tensor-product vectors is performed for each subspace individually. First Length[emph[a]] is evaluated and remaining Length[emph[b]]-Length[emph[a]] subspaces are left alone. The resulting state is thus of the form \[LeftAngleBracket]{emph[a]},{emph[b1]}\[RightAngleBracket] Ket[b2], where Length[emph[b1]]==Length[emph[a]] and emph[b] == emph[b1]~Join~emph[b2]. Analogously for the case when Length[emph[b]]<Length[emph[a]].
 6. Suppose we create a ket Ket[a,b] with as yet not defined values for Ket[a] and Ket[b]. When we define these values afterwards and then reevaluate the expression Ket[a,b], this automatically updates according to definition for Ket[a] and Ket[b]. Analogous functionality is implemented also for Bra and AngleBracket.
 7. Norm of the ket Ket[a] and bra Bra[a] can be given as Norm[Ket[a]] and Norm[Bra[a]], respectively. Norm command also accepts linear combinations of vectors. To get normalized version of the vector, one can use Normalize command.
 8. Partial trace of Ket[i1,\[Ellipsis],in] over subspaces {j1,\[Ellipsis],jk} is given by partTr[Ket[i1,\[Ellipsis],in],{j1,\[Ellipsis],jn}]. For more information type ?partTr.
 9. Trace of Ket[i1,\[Ellipsis],in] is given by Tr[Ket[i1,\[Ellipsis],in]]. Trace works also for Bras and for linear combinations of Kets and Bras
 10. The most frequently used kets are implemented as follows:
	"<>"{k0,k1}={Ket[0],Ket[1]}
	"<>"{kd,ka,kr,kl} = {Ket[d], Ket[a], Ket[r], Ket[l]} = "
	<>"{\!\(\*FractionBox[\(Ket[0] + Ket[1]\), SqrtBox[\(2\)]]\), \!\(\*FractionBox[\(Ket[0] - Ket[1]\), SqrtBox[\(2\)]]\), \!\(\*FractionBox[\(Ket[0] + \[ImaginaryI]\\\ Ket[1]\), SqrtBox[\(2\)]]\), \!\(\*FractionBox[\(Ket[0] - \[ImaginaryI]\\\ Ket[1]\), SqrtBox[\(2\)]]\)}
	"<>"{phip, phim, psip, psim} = {Ket[SuperPlus[\[CapitalPhi]]], Ket[SuperMinus[\[CapitalPhi]]], Ket[SuperPlus[\[CapitalPsi]]], Ket[SuperMinus[\[CapitalPsi]]]} = "
	<>"{\!\(\*FractionBox[\(Ket[0, \\\ 0]\\\  + \\\ Ket[1, \\\ 1]\), SqrtBox[\(2\)]]\),\!\(\*FractionBox[\(Ket[0, \\\ 0]\\\  - \\\ Ket[1, \\\ 1]\), SqrtBox[\(2\)]]\),\!\(\*FractionBox[\(Ket[0, \\\ 1]\\\  + \\\ Ket[1, \\\ 0]\), SqrtBox[\(2\)]]\), \!\(\*FractionBox[\(Ket[0, \\\ 1]\\\  - \\\ Ket[1, \\\ 0]\), SqrtBox[\(2\)]]\)}"
	];


Bra::usage="Built-in command Bra is overloaded, so one can use it as usual bra vectors. For more info see usage of Ket.";


Ket[a1_,a2__]/;Or@@(Function[$$x,ValueQ[Ket[$$x]],HoldAll]/@Unevaluated[{a1,a2}]):=CircleTimes@@(Ket/@Unevaluated[{a1,a2}])
Bra[a1_,a2__]/;Or@@(Function[$$x,ValueQ[Bra[$$x]],HoldAll]/@Unevaluated[{a1,a2}]):=CircleTimes@@(Bra/@Unevaluated[{a1,a2}])
(*these two lines are due to situation when we create a tensor product of Kets and Bras that have not been undefined yet; if we define
these afterwards we expect the already created tensor product to update accordingly during reevaluation;
without this line this feature would not work*)


(* ::Subsubsection::Closed:: *)
(*linearCombinationQ*)


(* ::Text:: *)
(*Is the expression a linear combination (of Kets or Bras)*)


linearCombinationQ::usage=toNiceFormBraKet@"linearCombinationQ[emph[val]_, emph[patt]_]: Checks whether argument emph[val] is a linear combination of constructs matching pattern emph[patt].";


SyntaxInformation[linearCombinationQ]={"ArgumentsPattern"->{_,_}};


SetAttributes[linearCombinationQ,HoldRest];


linearCombinationQ[val_, patt_] := (Head@Expand[val] === Plus && AllTrue[Expand[val], MatchQ[#, _. patt] &]) || (MatchQ[val, _. patt])


(*linearCombinationQ[val_, head_] := (Head@Expand[val] === Plus && AllTrue[Expand[val], MatchQ[#, _. _head] &]) || (MatchQ[val, _. _head])*)


(* ::Subsubsection::Closed:: *)
(*addKetBraDownValue*)


(* ::Text:: *)
(*Assignments to Kets and Bras*)


SetAttributes[addKetBraDownValue,HoldAll]


addKetBraDownValue::usage=toNiceFormBraKet["This routine substitutes Set routine for Kets and Bras. When one assigns a value to Ket[something], then automatically its adjoint is assigned to Bra[something]. The same works when we first assign a value to Bra[something]. Moreover, it is ensured that no value can be assigned to Ket[k], where emph[k] is some integer or emph[idket] token."];
addKetBraDownValue::notone="Assignments to empty or tensor-product Kets or Bras are forbidden.";
addKetBraDownValue::basisvec=toNiceFormBraKet["No values are allowed to be assigned to Ket[k], where emph[k] is some integer. These vectors are assumed to be basis vectors."];
addKetBraDownValue::idket="Symbol emph[idket] is reserved to stand for the identity mapping. No value can be assigned to it.";
addKetBraDownValue::ketbramismatch="The right-hand side of the assignment is not a linear combination of `1`s.";
addKetBraDownValue::basvec="Ket `` is a basis vector in basis '``'";


addKetBraDownValue[arg___,val_,type_]:=Module[{bas},
	If[Length[{arg}]!=1,
		Message[addKetBraDownValue::notone];Return[]];
	If[Unevaluated[arg]===idket,
		Message[addKetBraDownValue::idket];Return[]];
	If[!linearCombinationQ[val,type],Message[addKetBraDownValue::ketbramismatch,type];Return[]];
	
	bas=SelectFirst[Keys@onBases[],basisVectorQ[#,Ket[arg]]&,None];
	If[bas=!=None,
		Message[addKetBraDownValue::basvec,Ket[arg],bas];Return[]];
	
	Quiet[{Ket[arg]=.,Bra[arg]=.}];
	AppendTo[DownValues[Ket],HoldPattern[Ket[arg]]->(*\[RuleDelayed]*)Evaluate[val]];
	AppendTo[DownValues[Bra],HoldPattern[Bra[arg]]->(*\[RuleDelayed]*)Evaluate[(val)\[ConjugateTranspose]]];
	val
]


Ket/:Set[Ket[s___],rhs_]:=addKetBraDownValue[s,rhs,_Ket]
Bra/:Set[Bra[s___],rhs_]:=addKetBraDownValue[s,rhs,_Bra]


(* ::Subsubsection::Closed:: *)
(*Adjoints of Kets and Bras*)


ConjugateTranspose[Ket[s___]]^:=Bra[s]
ConjugateTranspose[Bra[s___]]^:=Ket[s]


(* ::Subsubsection::Closed:: *)
(*Distributive Properties of ConjugateTranspose*)


Unprotect[ConjugateTranspose];


ConjugateTranspose[expr_Plus]:=ConjugateTranspose/@expr
ConjugateTranspose[coef_?(FreeQ[#,Ket|Bra]&) expr_]:=(coef)\[Conjugate] ConjugateTranspose[expr]


ConjugateTranspose[number_?NumericQ]:=(number)\[Conjugate]


Protect[ConjugateTranspose];


(* ::Subsubsection::Closed:: *)
(*Properties of NonCommutativeMultiply*)


(* ::Text:: *)
(*NonCommutativeMultiply corresponds to scalar product and constructs of the form Ket[a]Bra[b].*)


Unprotect[NonCommutativeMultiply];


a_**(b_?(FreeQ[#,Bra|Ket]&) c_):=b a**c
(a_?(FreeQ[#,Bra|Ket]&) b_)**c_:=a b**c
a_**b_Plus:=(a**#)&/@b
a_Plus**b_:=(#**b)&/@a
a_?NumericQ**b_?NumericQ:=a b


ConjugateTranspose[Ket[k___]**Bra[b___]]^:=Ket[b]**Bra[k]


Protect[NonCommutativeMultiply];


SetAttributes[Bra,{HoldAll,ReadProtected}]
SetAttributes[Ket,{HoldAll,ReadProtected}]


(*Ket[a___]**Ket[b___]^:=Ket[a,b]
Bra[a___]**Bra[b___]^:=Bra[a,b]
*)
Ket[a___]**coef_?(FreeQ[#,Bra|Ket]&)^:=coef Ket[a]
coef_?(FreeQ[#,Bra|Ket]&)**Ket[a___]^:=coef Ket[a]

Bra[a___]**coef_?(FreeQ[#,Bra|Ket]&)^:=coef Bra[a]
coef_?(FreeQ[#,Bra|Ket]&)**Bra[a___]^:=coef Bra[a]


Bra[a__]**Ket[b__]^:=AngleBracket[{a},{b}]


(* ::Subsubsection::Closed:: *)
(*Properties of CircleTimes*)


(* ::Text:: *)
(*CircleTimes corresponds to the Kronecker product of Kets, Bras and KetBras.*)


Unprotect[CircleTimes];


SetAttributes[CircleTimes,Flat];


(*linearity*)
a_\[CircleTimes](b_?(FreeQ[#,Bra|Ket]&) c_):=b a\[CircleTimes]c
(a_?(FreeQ[#,Bra|Ket]&) b_)\[CircleTimes]c_:=a b\[CircleTimes]c
a_\[CircleTimes]b_Plus:=(a\[CircleTimes]#)&/@b
a_Plus\[CircleTimes]b_:=(#\[CircleTimes]b)&/@a


(*properties for Kets and Bras*)
Ket[a___]\[CircleTimes]Ket[b___]:=Ket[a,b]
Bra[a___]\[CircleTimes]Bra[b___]:=Bra[a,b]

(*CircleTimes[Ket[a__]]^:=Ket[a]
CircleTimes[Bra[a__]]^:=Bra[a]*)

(a:(_Ket|_Bra))\[CircleTimes](b_?(FreeQ[#,Bra|Ket]&)):=b a
(a_?(FreeQ[#,Bra|Ket]&))\[CircleTimes](c:(_Ket|_Bra)):=a c


(*(*for scalars return usual product*)
(*any problem with this?*)
a_?(FreeQ[Bra|Ket])\[CircleTimes]b_?(FreeQ[Bra|Ket]):=a b*)


(*properties for KetBras*)
Ket[ak___]**Bra[ab___]\[CircleTimes]Ket[bk___]**Bra[bb___]:=Ket[ak,bk]**Bra[ab,bb];
(a:(Ket[___]**Bra[___]))\[CircleTimes](b_?(FreeQ[#,Bra|Ket]&)):=b a;
(a_?(FreeQ[#,Bra|Ket]&))\[CircleTimes](c:(Ket[___]**Bra[___])):=a c;


Protect[CircleTimes];


(* ::Subsubsection::Closed:: *)
(*kroneckerKetProducts*)


(* ::Text:: *)
(*kroneckerKetProducts basically creates multipartite basis out of bases of individual unipartite spaces.*)


kroneckerKetProducts::usage=toNiceFormBraKet@"kroneckerKetProducts[emph[list1], emph[list2], ...]: Returns a list of Kets corresponding to Kronecker product of Kets from emph[list1], emph[list2], etc. respectively.
kroneckerKetProducts[emph[list1], emph[num]]: This is equivalent to kroneckerKetProducts[emph[list1], emph[list1], ...], where emph[list1] appears emph[num] times.";


SyntaxInformation[kroneckerKetProducts]={"ArgumentsPattern"->{__}};


kroneckerKetProducts::invnum="Invalid Kronecker product power ``.";


kroneckerKetProducts[seq:{__Ket}..]:=Module[{},
	If[Length[{seq}]==1,Return[seq]];
	(*Flatten@Outer[NonCommutativeMultiply,##]&@@{seq}*)
	CircleTimes@@@Tuples[{seq}]
]


kroneckerKetProducts[list:{__Ket},num_Integer]:=Module[{},
	If[num<=0,Message[kroneckerKetProducts::invnum,num];Return[]];
	If[num==1,Return[list]];
	CircleTimes@@@Tuples[list,num]
]


(* ::Subsubsection::Closed:: *)
(*permuteKets*)


permuteKets::usage="permuteKets[emph[expr]_,emph[perm]_List]: For linear combination emph[expr] of Kets with the same number of subspaces, return the same combination where subspaces are permuted according to permutation emph[perm].";


permuteKets::notket="Input expression is not a linear combination of Kets.";
permuteKets::invperm="Invalid permutation `1` for number `2` of unipartite subspaces.";
(*for permuteKets::diffsub see General::diffsub*)


SyntaxInformation[permuteKets]={"ArgumentsPattern"->{_,_}};


permuteKets[expr_,perm_List]:=
	Module[{locexpr=expr,raw,coefs,specs,len},
		If[!linearCombinationQ[expr,Ket[__]],Message[permuteKets::notket];Return[]];
		locexpr=Collect[locexpr,_Ket];
		
		(*extract coefficients and Ket specifications from expr*)
		If[Head[locexpr]=!=Plus,locexpr={locexpr}];
		raw=Cases[locexpr,coef_. Ket[k__]:>{coef,Ket[k]}];
		{coefs,specs}=Transpose@SortBy[raw,Last];
		
		len=Union[Length/@specs];
		If[Length@len>1,Message[permuteKets::diffsub];Return[],len=First[len]];
		If[Sort[perm]!=Range[len],Message[permuteKets::invperm,perm,len];Return[]];

		(*permute subspaces*)
		specs=Permute[#,perm]&/@specs;
		coefs . specs
	]


(* ::Subsubsection::Closed:: *)
(*parseKetSpecs and parseKetBraSpecs*)


General::invalket="Input expression is not a linear combination of terms Ket[x].";


parseKetSpecs[expr_,funname_:General] := Module[{locexpr,collexpr,raw, coefs, specs, outspace, inspace},

	(*make sure no duplicities occur and that expr is valid*)
	collexpr=Collect[expr, Ket[__]];
	If[!linearCombinationQ[expr, Ket[__]], Message[funname::invalket]; Return[$Failed]];
	
	(*extract coefficients and Ket specifications from expr*)
	locexpr=If[MatchQ[collexpr, _. Ket[__]],{collexpr},collexpr];
	raw = Cases[locexpr, coef_. Ket[k__] :> {coef, Ket[k]}];
	{coefs, specs} = Transpose@SortBy[raw, Last];
	
	(*return everything*)
	{collexpr,coefs, specs}
  ]


General::invalketbra="Input expression is not a linear combination of terms Ket[x]**Bra[y].";


parseKetBraSpecs[expr_,funname_:General] := Module[{locexpr,collexpr,raw, coefs, specs},

	(*make sure no duplicities occur and that expr is valid*)
	collexpr=Collect[expr, Ket[__]**Bra[__]];
	If[!linearCombinationQ[expr, Ket[__] ** Bra[__]], Message[funname::invalketbra]; Return[$Failed]];
	
	(*extract coefficients and KetBra specifications from expr*)
	locexpr=If[MatchQ[collexpr, _. Ket[__] ** Bra[__]],{collexpr},collexpr];
	raw = Cases[locexpr, coef_. Ket[k__] ** Bra[b__] :> {coef, {Ket[k], Ket[b]}}];
	{coefs, specs} = Transpose@SortBy[raw, Last];
	
	(*return everything*)
	{collexpr,coefs,specs}
  ]


(* ::Title::Closed:: *)
(*Change of Basis*)


(* ::Subsubsection::Closed:: *)
(*Auxiliary routines*)


replaceKetInternal[expr_,iraw_,sub_,locpatt_]:=
	Module[{raw=iraw,auxraw,auxsub},

		(* *** first, generate replacement rules *** *)

		(*a little trick, since CircleTimes[Ket[x]] cannot be defined to be
			 just Ket[x], here is a workaround; in order to get rid of
			 CircleTimes[Ket[x]] terms in the final output of the routine, we add
			 one element containing just number 1 and no Ket;from properties of
			 CircleTimes we effectively get rid of the unwanted expression*)
		auxraw={##,1}&@@@raw[[All,2]];
			
		(*if sub is All, then perform directly substitution, if specific list of indices
		 sub is given, apply substitution only to the specified subsystems*)
		Which[
			sub===All,
			raw[[All,2]]=CircleTimes@@@(auxraw/.locpatt);
			,
			MatchQ[sub,{__Integer?Positive}],
		
			(*for convenience, if term of auxraw has n elements, then auxsub[[n]] is a list
			 of valid positions where MapAt is to be applied, this is useful when n is less
			 than maximum index in locsub*)
			(* 
			(*probably slower version*)
			locsub=List/@Union[sub];
			auxsub=Table[TakeWhile[locsub,First@#\[LessEqual]i&],{i,0,Max[Length/@auxraw]}];
			*)	
			(*probably faster version*)
			auxsub=Module[{i=1,k=1,n=Max[Length/@auxraw],ss},
				ss=PadRight[Union[sub],n,n+1];
				Rest@NestList[(If[i++>=ss[[k]],Append[#,{ss[[k++]]}],#])&,{},n]
			];
	
			(*perform substitution only in positions specified by auxsub and then make a tensor
			product*)
			raw[[All,2]]=(CircleTimes@@
				MapAt[ReplaceAll[locpatt],#,auxsub[[Length[#]]]])&/@auxraw;
			,
			True,
			Message[replaceKet::invsub];Return[];
		];
			
			
		(* *** second, apply the replacement rules *** *)	
		raw=Rule@@@DeleteCases[raw,{a_,a_}];
		expr/.raw
]


(* ::Subsubsection::Closed:: *)
(*replaceKet for Kets and KetBras*)


(* ::Text:: *)
(*Replacement of unipartite Kets in lin. comb. of multipartite Kets*)


replaceKet::usage=toNiceFormBraKet@"replaceKet[emph[expr]_,emph[patt]_,emph[sub]_]: In a linear combination emph[expr] of Kets of the form Ket[a1, a2, a3, etc] replaces expressions Ket[ai] according to pattern emph[patt]. The third, optional, argument specifies in which subsystem the replacement should be performed. For instance, replaceKet[Ket[1,b]+2.3 Ket[0,2,8]+Ket[b],{Ket[b]->Ket[-5],Ket[8]->Ket[c]},{1,3}] returns Ket[-5]+Ket[1,b]+2.3 Ket[0,2,c], since substitution is not done in the second subsystem. In emph[patt] only unipartite replacement rules are allowed. If there is only one subsystem one wants to perform substitution in, one can omit braces and as emph[sub] specify just the integral index. If the third argument is omitted, the substitutions are done in all subsystems.";


SyntaxInformation[replaceKet]={"ArgumentsPattern"->{_,_,___}};


replaceKet::invsub="Invalid subspace index specification. Subspace may be identified only by a positive integer. Alternatively, token All may be used instead of list of indices.";
replaceKet::invpatt="Some or all replacement rules are not of the form Ket[a_]->Ket[b_]. Calculation proceeds though.";


replaceKet[expr_,patt_,sub_Integer?Positive]:=replaceKet[expr,patt,{sub}]


replaceKet[expr_?(linearCombinationQ[#,_Ket]&),patt_,sub_:All]:=
	Module[{locexpr,raw,coefs,specs,locpatt=patt,locsub},

		(*get specifications*)
		(*raw is a list of doubles of the form {Ket[a,b,c,...],{Ket[a],Ket[b],Ket[c],...}}*)
		{locexpr,coefs,specs}=parseKetSpecs[expr,replaceKet];
		raw={#,List@@(Ket/@#)}&/@specs;
		If[raw=={},Return[expr]];
					
		(*check whether replacement rule(s) makes sense*)
		If[Head[locpatt]=!=List,locpatt={locpatt}];
		If[Not@AllTrue[locpatt,MatchQ[Rule[_Ket,_?(linearCombinationQ[#,_Ket]&)]]],
			Message[replaceKet::invpatt]];
			
		(*perform the actual replacement*)
		replaceKetInternal[expr,raw,sub,locpatt]
	]


replaceKet[expr_?(linearCombinationQ[#,Ket[__]**Bra[__]]&),patt_,sub_:All]:=
	Module[{locexpr,ketraw,braraw,coefs,specs,ketpatt=patt,brapatt,ketlist,bralist},

		(*get specifications*)
		(*ketraw and braraw are lists of doubles of the form {Ket[a,b,c,...],{Ket[a],Ket[b],Ket[c],...}}*)
		{locexpr,coefs,specs}=parseKetBraSpecs[expr,replaceKet];
		{ketlist,bralist}=Transpose@specs;
		ketraw={#,List@@(Ket/@#)}&/@ketlist;
		braraw={#,List@@(Ket/@#)}&/@bralist;
		If[ketraw=={}&&braraw=={},Return[expr]];
		braraw=braraw/.Ket->Bra;
					
		(*check whether replacement rule(s) makes sense*)
		If[Head[ketpatt]=!=List,ketpatt={ketpatt}];
		If[Not@AllTrue[ketpatt,MatchQ[Rule[_Ket,_?(linearCombinationQ[#,_Ket]&)]]],
			Message[replaceKet::invpatt]];
		brapatt=Map[ConjugateTranspose,ketpatt,{2}];
			
		(*perform the actual replacement*)
		locexpr=replaceKetInternal[expr,ketraw,sub,ketpatt];
		locexpr=replaceKetInternal[locexpr,braraw,sub,brapatt];
		locexpr
	]


(* ::Subsubsection::Closed:: *)
(*changeBasis*)


changeBasis::usage=toNiceFormBraKet@"changeBasis[emph[expr],emph[frombasis]_String,emph[tobasis]_String,emph[sub]_:All]: In emph[expr] replace kets from basis emph[frombasis] with their form expressed in basis emph[tobasis]. If emph[sub] is specified, then it should be the number of subspace(s) in which the substitution is to be made. For instance, emph[sub]={1,3} means the substitution is made only for emph[a1] and emph[a3] in kets of the form Ket[a1,a2,a3,etc].";


changeBasis::invfrom="Input basis specification is not valid. Only finite bases are allowed.";
changeBasis::invto="Output basis specification is not valid. Only finite bases are allowed.";


changeBasis[expr_,frombasis_String->tobasis_String,sub_:All]:=changeBasis[expr,frombasis,tobasis,sub]


changeBasis[expr_,frombasis_String,tobasis_String,sub_:All]:=Module[{patt,inkets,outkets,lincombs},

	(*are basis specifications valid?...*)
	If[Not@basisQ[frombasis]||infiniteBasisQ[frombasis],
		Message[changeBasis::invfrom];Return[]];
	If[Not@basisQ[frombasis]||infiniteBasisQ[frombasis],
		Message[changeBasis::invto];Return[]];

	{inkets,outkets}={onBases[frombasis],onBases[tobasis]};
	lincombs=$onBasesTransformations[{tobasis,frombasis}] . outkets;
	patt=Thread[inkets->lincombs];
	replaceKet[expr,patt,sub]
]


(* ::Title::Closed:: *)
(*(Partial) Trace*)


(* ::Subsubsection::Closed:: *)
(*Auxiliary routines*)


partialTraceKetBras[ketlist_,bralist_,coefs_,ketlen_,bralen_,locsubsp_]:=
	Module[{chars,substrules,revrules,ketlistint,locketlen=ketlen,bralistint,listint,dims,trace,
		sparsecoef},
		
		(*get all unique characters in ket specifications*)
		chars=DeleteDuplicates@Flatten[Hold@@(Join[ketlist,bralist]/.Ket->Hold)];
		
		(*create substitution rules that to each character assign an integer*)
		substrules=Thread[chars->Hold@@Range[Length[chars]],Hold];
		substrules=substrules/.(a_->b_):>(HoldPattern[a]->b);
		substrules=List@@substrules;
		
		(*create reverse rules*)
		revrules=(#2->#1)&@@@substrules;
		
		(*in subspaces to be traced over replace idkets with appropriate basis vectors*)
		(*KDYZTAK DODELAT*)
		
		(*integral counterparts of ketlist and bralist are ketlistint and bralistint, 
		respectively, this is fed into SparseArray*)
		ketlistint=List@@@(ketlist/.substrules);
		bralistint=List@@@(bralist/.substrules);
		listint=Join@@@Transpose[{ketlistint,bralistint}];
		
		(*determine dimensions of individual subsystems since SparseArray needs it; the following
		line does not really calculate dimensions, but is probably sufficient for SparseArray to
		work correctly*)
		dims=Table[Max[listint],locketlen+bralen];
		
		(*create sparse array of coefficients*)
		sparsecoef=SparseArray[listint->coefs,dims];
		
		(*use partial trace routine for tensors*)
		trace=TensorContract[sparsecoef,{#,#+locketlen}&/@locsubsp];
		locketlen-=Length[locsubsp];
		
		(*if we traced over all subspaces, so that we obtain the trace, return trace*)
		If[Head[trace]=!=SparseArray,Return[trace]];
		
		(*from resulting array of coefficients go back to the ket notation*)
		trace=Most[ArrayRules[trace]];
		trace={#2,TakeDrop[#1,locketlen]}&@@@trace;
		trace=(#1 Ket@@(First[#2]/.revrules)**Bra@@(Last[#2]/.revrules))&@@@trace;
		
		(*return the sum of corresponding terms*)
		ReleaseHold@Total[trace]
	]


(* ::Subsubsection::Closed:: *)
(*partTr for Kets and KetBras*)


(* ::Text:: *)
(*Partial Trace of Expression*)


partTr::usage=toNiceFormBraKet["partTr[emph[vec]_, emph[subsp]_]: Partial trace of expression emph[vec]"<>" \[Element] \!\(\*SubscriptBox[\(\[ScriptCapitalH]\), \(1\)]\)\[TensorProduct]\[Ellipsis]\[TensorProduct]\!\(\*SubscriptBox[\(\[ScriptCapitalH]\), \(n\)]\) over subspaces \!\(\*SubscriptBox[\(\[ScriptCapitalH]\), \(j\)]\),"<>" where all emph[j]-s are specified by list emph[subsp]; emph[vec] may be a linear combination of Kets or Ket**Bras. It is assumed that each character in emph[vec] vector specifications corresponds to a single subsystem. Bases of subspaces over which the partial trace is done are identified automatically. If some vectors cannot be identified, an error is thrown. Indices in emph[subsp] may also be specified by negative numbers. Instead of list emph[subsp] one may use token All, in which case usual trace is performed over all subspaces. NOTE: for lin. comb. of Ket[k__]**Bra[b__], dimension emph[dimk] of emph[k]-s must be equal for all terms (analogously emph[dimb] for emph[b]-s), but emph[dimk] does not need to be equal to emph[dimb]. In such a case emph[subsp] must contain indices that are valid index specification of list of length Min[emph[dimk],emph[dimb]].\npartTr[emph[mat]_, emph[subsp]_,emph[dim]_]: Partial trace of matrix emph[mat] corresponding to a state of emph[dim]-dimensional subsystems (number of subsystems is derived from dimensions of emph[mat] and dimension(s) emph[dim]). For subsystems with different dimensions, emph[dim] can be input as a list of dimensions. Only for square matrices the trace is calculated."];


SyntaxInformation[partTr]={"ArgumentsPattern"->{_,__}};


partTr::diffdim="Input expression is a linear combination of vectors with different number of dimensions.";
partTr::outofran="Subspace specification indices `1` are out of range {-`2`,`2`}\[Backslash]{0}. (Counting starts with 1, not 0.)";
partTr::diffdimket="Input expression is a linear combination of vectors with different number of dimensions in ket specifications.";
partTr::diffdimbra="Input expression is a linear combination of vectors with different number of dimensions in bra specifications.";
partTr::invbases="Some of the vectors in the input are not valid basis vectors.";


partTr[vec_?(linearCombinationQ[#,_Ket]&),subsp:{__Integer}|All]:=
	Module[{locexpr,coefs,specs,len,locsubsp=subsp,listval,bases,ketlist,bralist,ketlen,bralen},

		(*get specifications*)
		{locexpr,coefs,specs}=parseKetSpecs[vec,partTr];
		len=Union[Length/@specs];
		If[Length[len]==1,len=First[len],Message[partTr::diffdim];Return[]];
	
		(*is subsp token All?*)
		If[locsubsp===All,locsubsp=Range[len]];
		
		(*is subsp valid list of indices to trace over?*)
		If[AllTrue[locsubsp,(-len<=#<=len&&#!=0.)&],
			locsubsp=Union@Mod[locsubsp,len+1],
			Message[partTr::outofran,locsubsp,len];Return[]
		];

		(*are all vectors in vec (after evaluation) basis vectors?*)
		(*if the vectors do not belong to any basis, we do not know whether they are ON*)
		(*if they are not ON, the partial trace gives wrong results*)
		listval=specs[[All,locsubsp]];
		bases=Quiet@Check[identifyBases[Evaluate@listval,True],$Failed];
		If[bases===$Failed,Message[partTr::invbases];Return[]];

		(*turn ket specifications into effective ketbra specifications*)
		ketlist=Flatten[Table[#,Length[specs]]&/@specs,1];
		bralist=Flatten[Table[specs,Length[specs]],1];
		coefs=Flatten[Outer[Times,coefs\[Conjugate],coefs],1];

		(*perform the actual partial trace*)
		partialTraceKetBras[ketlist,bralist,coefs,len,len,locsubsp]
	];


partTr[expr_?(linearCombinationQ[#,Ket[__]**Bra[__]]&),subsp:{__Integer}|All]:=
	Module[{locexpr,listval,bases,coefs,ketlist,bralist,ketlen,bralen,len,locsubsp=subsp,specs},

		(*get specifications*)
		{locexpr,coefs,specs}=parseKetBraSpecs[expr,partTr];
		{ketlist,bralist}=Transpose@specs;
		
		(*is expr combination of ket**bras of the same dimension?*)
		ketlen=Union[Length/@ketlist];
		bralen=Union[Length/@bralist];
		If[Length[ketlen]==1,ketlen=First[ketlen],Message[partTr::diffdimket,ketlen];Return[]];
		If[Length[bralen]==1,bralen=First[bralen],Message[partTr::diffdimbra,bralen];Return[]];
		len=Min[{ketlen,bralen}];
	
		(*is subsp token All?*)
		If[locsubsp===All,locsubsp=Range[len]];
		
		(*is subsp valid list of indices to trace over?*)
		If[AllTrue[locsubsp,(-len<=#<=len&&#!=0.)&],
			locsubsp=Union@Mod[locsubsp,len+1],
			Message[partTr::outofran,locsubsp,len];Return[]
		];
	
		(*are all vectors in vec (after evaluation) basis vectors?*)
		(*if the vectors do not belong to any basis, we do not know whether they are ON*)
		(*if they are not ON, the partial trace gives wrong results*)
		listval=ketlist[[All,locsubsp]];
		bases=Quiet@Check[identifyBases[Evaluate@listval,True],$Failed];
		If[bases===$Failed,Message[partTr::invbases];Return[]];
		
		listval=bralist[[All,locsubsp]];
		bases=Quiet@Check[identifyBases[Evaluate@listval,True],$Failed];
		If[bases===$Failed,Message[partTr::invbases];Return[]];

		(*perform the actual partial trace*)
		partialTraceKetBras[ketlist,bralist,coefs,ketlen,bralen,locsubsp]
	];


(* ::Subsubsection::Closed:: *)
(*partTr of Matrix*)


partTr::invdims = "Dimensions `1` of input matrix do not correspond to density matrix of `2`-partite state of `3`-dimensional systems.";
partTr::invdimsdiff = "Dimensions `1` of input matrix do not correspond to density matrix of `2` systems with respective dimensions `3` (Times@@`3` = `4` != First@`1`).";


partTr[mat_?MatrixQ,subsp_:{__Integer}|All,dim_Integer]:=
	Module[{num},
		(*from length of mat and dimension infer number of subsystems*)
		num=Log[dim,Length[mat]];
		If[Dimensions[mat]!={dim^num,dim^num},Message[partTr::invdims,Dimensions[mat],num,dim];
			Return[]];
			
		partTr[mat,subsp,Table[dim,num]]
	]


partTr[mat_?MatrixQ,subsp_:{__Integer}|All,dims_List]:=
	Module[{locsubsp=subsp,trmat,num},
		(*from length of mat and dimension infer number of subsystems*)
		num=Length[dims];
		If[Dimensions[mat]!={Times@@dims,Times@@dims},
			Message[partTr::invdimsdiff,Dimensions[mat],num,dims,Times@@dims];Return[]
		];

		(*is subsp token All?*)
		If[locsubsp===All,locsubsp=Range[num]];
		
		(*is subsp valid list of indices to trace over?*)
		If[AllTrue[locsubsp,(-num<=#<=num&&#!=0.)&],
			locsubsp=Union@Mod[locsubsp,num+1],
			Message[partTr::outofran,locsubsp,num];Return[]
		];
		
		trmat=Fold[Partition[#1,{#2,#2}]&,mat,Most@Reverse@dims];

		trmat=Echo@TensorContract[trmat,{2#-1,2#}&/@locsubsp];
		If[Echo@ArrayQ[trmat],ArrayFlatten[trmat],trmat]
	]


(* ::Subsubsection::Closed:: *)
(*Trace*)


Unprotect[Tr];
Tr[vec_?(linearCombinationQ[#,_Bra]&)]:=Tr[(vec)\[ConjugateTranspose]]
Tr[vec_?(linearCombinationQ[#,_Ket]&)]:=partTr[vec,All]
Protect[Tr];


(* ::Title::Closed:: *)
(*Factorization of Multipartite Terms*)


(* ::Subsubsection::Closed:: *)
(*Auxiliary routines*)


General::pownotone="Power of the term is not one, it is ``.";


processSingleTermPatt[ketrules_][{term_, power_}] := Module[{aux = term, holds, nums, state, kets,
	numrules = Hold[__, n_] :> n, coefs},
  
  If[power!=1,Message[processSingleTermKetBra::pownotone,power];Return[$Failed]];
  
  (*case with a single Hold is simple*)
  If[Head[aux] =!= Plus, Return[{{aux /. numrules}, aux /. ketrules}]];
  
  (*otherwise change lin. comb. into array*)
  aux = aux /. Plus -> List;
  aux=Replace[aux,x_Hold:>{1,x},{1}]/. Times -> List;
  holds = Replace[aux, Except[Hold[__]] -> Nothing, {2}];
  coefs = Times @@@ Replace[aux, Hold[__] -> Nothing, {2}];
  holds = SortBy[Last] /@ holds;
  nums = Union[holds /. numrules];
  If[Length[nums] > 1, Return[$Failed]];
  
  (*go from Hold to Ket*)
  kets = CircleTimes @@@ (holds /. ketrules);
  kets=kets/.CircleTimes[x_]:>(x/.CircleTimes->Identity);(*CircleTimes is Flat, hence the Identity trick*)
  
  (*return subspace specification and corresponding state*)
  {First[nums],coefs . kets}
  ]


factorTermsAndPostProcess[expr_,rules_,patt_]:=
	Module[{locexpr=expr,faclist,pos,posnonconst,posconst,const,nonconsts},

		(*turn multipartite Kets into a usual product 'creation' operators*)
		locexpr=locexpr/.rules;

		(*use FactorList to do the dirty job*)
		faclist=FactorList[locexpr];
		
		(*take positions of constants and non-constants*)
		pos=Position[faclist,_Hold];
		posnonconst=Union[First/@pos];
		posconst=Complement[Range[Length[faclist]],posnonconst];
		
		(*process constants*)
		const=Times@@(Power@@@faclist[[posconst]]);
		const={{{0},const}}; (*to comply with the output format*)
		
		(*process non-constants*)
		nonconsts=faclist[[posnonconst]];
		nonconsts=processSingleTermPatt[patt]/@nonconsts;
		
		If[MemberQ[nonconsts,$Failed],Message[factorKetsList::bobobo];Return[]];
		
		(*sort nonconsts according to subspace order number*)
		nonconsts=nonconsts[[Ordering[nonconsts[[All,1,1]]]]];
		
		(*join constants and nonconstants together*)
		faclist=Join[const,nonconsts];
		faclist
]


(* ::Subsubsection::Closed:: *)
(*factorKetsList*)


factorKetsList::usage=toNiceFormBraKet@"factorKetsList[emph[expr]_]: Works similarly to FactorList, but the format of output is different. If emph[expr] is a linear combination of multipartite Kets, it returns individual factors out of which emph[expr] is composed. The output format is as follows: {{{0},emph[commonConstants]},{{emph[orderOfSubspace1]},emph[correspondingSubexpression1]}, ..., {{emph[orderOfSubspaceN]},emph[correspondingSubexpressionN]}}.";


SyntaxInformation[factorKetsList]={"ArgumentsPattern"->{_}};


General::diffdim="Input expression is a linear combinations of terms with different number of subsystems. Such input expressions are not supported.";


factorKetsList[expr_?(linearCombinationQ[#, Ket[__]] &)]:=
	Module[{locexpr,coefs,specs,rules,patt},
		
		{locexpr,coefs,specs}=parseKetSpecs[expr,factorKetsList];
		If[Length@Union[Length/@specs]>1,Message[factorKetsList::diffdim];Return[]];
		
		(*rules for turning multipartite Kets into a usual product 'creation' operators*)
		(*complicated form of rules makes sure that specifications inside Kets are not evaluated*)
		rules=k_Ket:>Times@@(Hold@@@Transpose[{List@@(Ket/@k),Range[Length[k]]}]/.Ket[a__]:>a);
		patt=Hold[x_, _] :> Ket[x];
		
		factorTermsAndPostProcess[locexpr,rules,patt]
	]


factorKetsList[expr_?(linearCombinationQ[#, Ket[__]**Bra[__]] &)]:=
	Module[{locexpr,coefs,specs,rules,kets,bras,patt},
		
		{locexpr,coefs,specs}=parseKetBraSpecs[expr,factorKetsList];
		{kets,bras}=Transpose@specs;
		If[Length@Union[Length/@kets,Length/@bras]>1,Message[factorKetsList::diffdim];Return[]];
		
		(*rules for turning multipartite Kets into a usual product 'creation' operators*)
		(*complicated form of rules makes sure that specifications inside Kets are not evaluated*)
		rules=(k_Ket)**(b_Bra):>
			Times@@(Hold@@@Transpose[{CircleTimes@@@Transpose[{List@@(Ket/@k),List@@(Ket/@b)}],
			Range[Length[k]]}]/.Ket[a__]:>a);
		patt=Hold[x_,y_, _] :> Ket[x]**Bra[y];
		
		factorTermsAndPostProcess[locexpr,rules,patt]
	]


(* ::Subsubsection::Closed:: *)
(*unfactorKetsList*)


unfactorKetsList::usage = toNiceFormBraKet@"unfactorKetsList[emph[expr]_:{{{__},__}..}]: Takes output of factorKetsList and reconstructs the original expression. Argument emph[expr] should be a list of doubles, where the first element of each douple is a list of integers representing the order of subspaces present in the second element and the second element is either a Ket (Ket**Bra) or a lin. comb. of Kets (Ket**Bras) corresponding to that subspace.";


SyntaxInformation[unfactorKetsList]={"ArgumentsPattern"->{_}};


unfactorKetsList::noconst = "No constant term specificed. Halt.";


unfactorKetsList[expr : {{{__}, __} ..}] :=
	Module[{const,nonconst,loclist=expr,locexpr,ordering},
		
		(*get constant and nonconstant terms*)
		const = Cases[loclist, {{0}, c_} :> c];
		If[const == {}, Message[unfactorKetsList::noconst]; Return[], const = First[const]];
		nonconst = DeleteCases[loclist, {{0}, _}];
		
		(*ordering of subspaces*)
		ordering = Ordering@Flatten@nonconst[[All, 1]];
		
		(*from list create lin. comb.*)
		locexpr = const CircleTimes @@ (nonconst[[All, 2]]);
		locexpr = locexpr /. CircleTimes[x_] :> (x /. CircleTimes -> Identity);
		
		(*sort subspace specifications according to original positions*)
		locexpr /. k : (_Ket | _Bra) :> k[[ordering]]
	]


(* ::Title::Closed:: *)
(*Array vs Ket*)


(* ::Subsubsection::Closed:: *)
(*Auxiliary routines*)


General::diffsub="Specifications do not correspond to the same number of subspaces.";
General::multterm="Input expression contains multiple terms with the same specifications. Please first simplify input expression and then apply function again.";


generateBasisVectors::usage="generateBasisVectors[emph[basisname]_,emph[ind]_,emph[strspecs]_,emph[sp]_]: For finite basis emph[basisname] just return corresponding list of basis vectors. For infinite basis return a range of basis vectors, that either form consecutive series (when emph[sp] is True) or only necessary basis vectors for vector representation are returned (when emph[sp] is False). Argument emph[strspecs] are string representations of ket specficication and emph[ind] is an index of the specification in emph[strspecs] to be processed. generateBasisVectors already assumes that emph[basisname] is a valid basis name!";


generateBasisVectors[basisname_,ind_,strspecs_,sp_]:=
	Module[{locsp,lab,nums},
		(*for finite bases it is easy, just return the basis*)
		If[Not@infiniteBasisQ[basisname],Return[onBases[basisname]]];
		
		(*for infinite basis get first its label*)
		lab=First@getInfiniteLabel[basisname];
		If[basisname==="Integral",lab=""];
		
		(*get number specification of vectors in the input expression*)
		locsp=Union[strspecs[[All,First@ind]]];			
		nums=ToExpression[StringDrop[#,StringLength[lab]]&/@locsp];
		locsp=If[sp,Range@@MinMax[nums],nums];
	
		generateKets[basisname,locsp]
	];


createIdentifiedBasis::usage="createIdentifiedBasis[emph[bas]_,emph[specs]_,emph[span]_]: If given argument emph[bas] is 'Identify', then bases are identified in the specification emph[specs] and corresponding basis vectors are returned. If identified basis is infinite dimensional, two settings apply. Either emph[span] is False, in which case only the smallest necessary number of vectors is used from the infinite basis. If emph[span] is True, then vectors are taken from infinite basis such that they form consecutive range. If emph[bas] is an explicit list of Kets, then only it is checked whether the list contains duplicates. If not, it is returned, otherwise error is thrown. Argument emph[funsymb] is only a function that called this routine. The only purpose of this argument is that error messages are qualified by the calling function name.";


General::invbas="There are duplicates in given basis ``.";
General::unknownbas="Input expression contains elements for which input basis cannot be found. Please as the second argument specify also the basis in a form of a list of Ket specifications.";
General::morebas="More bases found in the input expression for given subspace(s).";


createIdentifiedBasis[bas:("Identify"|{__Ket}),specs_,span:(False|True),funsymb_]:=
	Module[{bases,locbas,strspecs,retbas},		
		
		(*which basis to choose*)
		Switch[bas,
			"Identify",
			
			(*identify basis*)
			(*first identify bases for each subspace*)
			bases=Quiet@Check[identifyBases[Evaluate@specs,True],
				Null,{identifyBases::difflen,identifyBases::notuniq}];
			Which[
				bases===Null,
				Message[funsymb::morebas];Return[];,
				
				MemberQ[bases,None],
				Message[funsymb::unknownbas];Return[];
			];				
			
			(*then for each basis name get its vectors and result store in locbas*)
			strspecs=getSpecs/@specs;
			retbas[basisname_,ind_]:=generateBasisVectors[basisname,ind,strspecs,span];
			locbas=MapIndexed[retbas,bases];
			
			(*from lists of unidim bases create multidim basis*)
			locbas=kroneckerKetProducts@@locbas;
			,		
									
			_,
			
			(*if basis is given explicitly, use that one*)
			bases=bas;
			If[Not@DuplicateFreeQ[bases,SameQ],Message[funsymb::invbas,bases];Return[];];
			locbas=bases;
		];

		locbas
]


General::invbas="Invalid basis ``.";
General::invbasspac="Invalid specified bases ``";
General::invnum="Invalid number `` of subspaces specified.";
General::notdiv="Length `1` of input vector is not consistent with given number of subspaces `2`.";
(*toKet::notmult="Length `1` of input vector is not equal to length of specified basis `2` taken to the power of given number of subspaces `3`.";*)
General::notprod="Lenght `1` of input vector is not equal to product `2` of lengths `3` of specified bases.";
General::moreinfbas="Not unique assignment of infinite bases. Only finite bases with at most one infinite basis, or only infinite bases with equal number of subspace dimensions are supported.";


checkAndCreateBasis::usage="checkAndCreateBasis[emph[bases]_,emph[len]_,emph[funsymb]_]: Take basis specifications emph[bases] and lenght of the List vector emph[len] and check if: 1) basis specifications are valid, 2) their dimensions fit the length emph[len]. If everything is meaningful, return corresponding basis, which can be directly used to transform List vector into Ket vector.";


checkAndCreateBasis[bases_,len_,funsymb_]:=
	Module[{locbas,finbas,infbas,lenfinbas,leninfbas,num=Length[bases],unidim},

		(*check validity of bases and for finite bases get their explicit forms*)
		locbas=
		Table[
			Which[
				MatchQ[basis,{Ket[_]..}],
				If[Not@DuplicateFreeQ[basis,SameQ],
					Message[funsymb::invbas,basis];Return[],
					basis	
				]
				,
				MatchQ[basis,_String]&&basisQ[basis],
				If[infiniteBasisQ[basis],
					basis,
					onBases[basis]
				]
				,
				True,
				$Failed
			],		
			{basis,bases}
		];
		
		(*are some specifications invalid?*)
		If[MemberQ[locbas,$Failed],Message[funsymb::invbasspac,Pick[bases,locbas,$Failed]];Return[]];
		
		(*take finite bases*)
		finbas=DeleteCases[locbas,_String];
		lenfinbas=Length/@finbas;
		If[len<Times@@lenfinbas,Message[funsymb::notprod,len,Times@@lenfinbas,lenfinbas];Return[]];
		
		(*take infinite bases*)
		infbas=Cases[locbas,_String];
		
		(*treat special cases*)
		Switch[
			{Length[finbas],Length[infbas]},
			
			{_?(#>=1&),0},
			(*if no infinite bases*)
			If[len!=Times@@lenfinbas,Message[funsymb::notprod,len,Times@@lenfinbas,lenfinbas];Return[]];
			,
			{_?(#>=1&),1},
			(*at least two infinite bases and one finite basis*)
			leninfbas=len/Times@@lenfinbas;
			If[Mod[leninfbas,1]!=0,Message[funsymb::notdiv,len,num];Return[]];
			locbas=Replace[locbas,bas_String:>generateKets[bas,leninfbas],2];
			,
			{_?(#>=1&),_?(#>=2&)},
			(*at least two infinite bases and at least one finite basis*)
			Message[funsymb::moreinfbas];Return[];
			,
			{0,_?(#>=1&)},
			(*if no finite bases*)
			unidim=len^(1/num);
			If[Mod[unidim,1]!=0,Message[funsymb::notdiv,len,num];Return[]];
			locbas=Replace[locbas,bas_String:>generateKets[bas,unidim],2];
			(*locbas=locbas/.bas_String:>generateKets[bas,unidim];*)
			,
			{_,_},
			Return[$Failed];
		];

		kroneckerKetProducts@@locbas
	]


(* ::Subsubsection::Closed:: *)
(*toKetBra*)


toKetBra::usage=toNiceFormBraKet@"toKetBra[emph[mat]_, emph[outbasis]_, emph[inbasis]_, emph[num]_]: From matrix emph[mat] creates corresponding operator expressed by ketbras. The second and third arguments, emph[outbasis] and emph[inbasis], specify bases (in the form of names of bases or lists of Kets) in which the operator is to be expressed. Argument emph[inbasis] may be omitted in which case it is taken to be identical to emph[outbasis]. Also the second argument may be omitted in which case both, the input and output bases are by default chosen to be integer bases with appropriate number of elements. Argument emph[num] specifies number of subspaces and by default it equals 1. For emph[num]==1 the number of basis vectors may exceed dimension of emph[mat]; for emph[num]>1, equalities emph[num]*Length/@{emph[outbasis],emph[inbasis]}==Dimensions[emph[mat]] have to be satisfied.";


SyntaxInformation[toKetBra]={"ArgumentsPattern"->{__}};


toKetBra::shortoutbas="There are `1` output basis vectors, but `2` are necessary.";
toKetBra::shortinbas="There are `1` input basis vectors, but `2` are necessary.";
toKetBra::invinbas="For `1` subspaces `2` input basis vectors are necessary, but `3` are given.";
toKetBra::outvinbas="For `1` subspaces `2` output basis vectors are necessary, but `3` are given.";
toKetBra::invbas="Invalid basis ``.";
toKetBra::invnum="Invalid number of subspaces ``.";
toKetBra::invindim="Input dimension `1` of the input matrix is not multiple of number of subspaces `2`.";
toKetBra::invoutdim="Output dimension `1` of the input matrix is not multiple of number of subspaces `2`.";


toKetBra[{{}},___]=0;


toKetBra[mat_]:=toKetBra[mat,{"Integral"},{"Integral"}]


toKetBra[mat_,inbases:{(_String|{Ket[_]..})..}]:=toKetBra[mat,inbases,inbases]


toKetBra[mat_,inbasis:(_String|{Ket[_]..}),num_Integer:1]:=Module[{},
	If[num<=0,Message[toKetBra::invnum,num];Return[];];
	toKetBra[mat,Table[inbasis,num],Table[inbasis,num]]
]


toKetBra[mat_?MatrixQ,outbases_List,inbases_List]:=
	Module[{dims=Dimensions[mat],locinbas,locoutbas,inlen,outlen,basvecmat},

		{outlen,inlen}=Dimensions[mat];
		
		(*get bases*)
		locoutbas=checkAndCreateBasis[outbases,outlen,toKetBra];
		locinbas=checkAndCreateBasis[inbases,inlen,toKetBra];
		If[locoutbas===Null||locinbas===Null,Return[]];
		
		(*matrix of elementary KetBras*)
		basvecmat=Outer[NonCommutativeMultiply,locoutbas,ConjugateTranspose/@locinbas,1,1];
		
		(*elementwise-multiply mat, matrix of coefficients, and basvecmat, matrix of individual KetBras*)
		(*resulting matrix then flatten and sum all terms*)
		Total@Flatten[mat basvecmat]
	]


(* ::Subsubsection::Closed:: *)
(*fromKetBra*)


fromKetBra::usage=toNiceFormBraKet@"fromKetBra[emph[expr]_, emph[outbasis]_, emph[inbasis]_]: From operator expressed as emph[expr] in terms of ketbras returns its matrix representation. Only operators acting on unipartite systems are allowed. The second and third arguments specify output and input bases in which the operator is expressed. If the third argument is omitted, it is taken to be identical to the second argument. If both, second and third, arguments are omitted, the input and output bases are inferred from emph[expr]. In such a case the minimum necessary number of basis vectors is chosen leading to a rectangular matrix, in general.";


SyntaxInformation[fromKetBra]={"ArgumentsPattern"->{__}};


fromKetBra::absent="Input expression contains basis ketbras `1` that cannot be constructed out of specified output basis `2` and input basis `3`.";


fromKetBra[expr_,basis_]:=fromKetBra[expr,basis,basis]
fromKetBra[expr_,outbasis:("Identify"|{__Ket}):"Identify",inbasis:("Identify"|{__Ket}):"Identify"]:=
	Module[{raw,outspace,inspace,specs,coefs,locinbas,locoutbas,pos,outer,absent,mat,locexpr},
		
		(*get KetBra specifications*)
		locexpr=parseKetBraSpecs[expr,fromKet];
		If[locexpr===$Failed,Return[],{locexpr,coefs, specs}=locexpr];
		
		If[Not@DuplicateFreeQ[specs],Message[fromKet::multterm];Return[]];
		If[Length@Union[Length/@specs]>1,Message[fromKet::diffsub];Return[]];
		
		(*get output space and input space specifications to define output and input bases, 
		if necessary*)
		{outspace,inspace}=Transpose[specs];
		
		(*identify input basis*)
		locinbas=createIdentifiedBasis[inbasis,inspace,False,fromKetBra];
		If[locinbas===Null,Return[]];
		
		(*identify output basis*)
		locoutbas=createIdentifiedBasis[outbasis,outspace,False,fromKetBra];
		If[locoutbas===Null,Return[]];
		
		(*auxiliary matrix for determination of nonzero terms in the resulting matrix*)
		outer=Outer[List,locoutbas,locinbas];
		
		(*find positions of nonzero terms*)
		pos=FirstPosition[outer,#]&/@specs;
		
		(*if bases do not contain all elements present in expr, throw an error*)
		absent=Flatten@Position[pos,_Missing];
		If[absent!={},
			absent=specs[[absent]];
			Message[fromKetBra::absent,#1**(#2\[ConjugateTranspose])&@@@absent,Short[locoutbas],Short[locinbas]];
			Return[]
		];

		(*create the resulting matrix and populate it with nonzero terms at appropriate 
		positions*)
		mat=SparseArray[{},{Length[locoutbas],Length[locinbas]}];
		(mat[[Sequence@@#1]]=#2)&@@@Transpose[{pos,coefs}];
		{mat,locoutbas,locinbas}
	]


(* ::Subsubsection::Closed:: *)
(*toKet*)


toKet::usage=toNiceFormBraKet@"toKet[emph[vec]_, emph[basis]_,emph[num]_]: From vector emph[vec] in List representation create its Ket representation in basis emph[basis]. Argument emph[basis] may be either Automatic (default value), or the name of ON basis, or a list of Kets. In the latter case the procedure only checks whether there are non-repeating Kets, it does not check whether they form valid basis. Additional optional parameter emph[num] may be given, which specifies number of subspaces out of which the total state consists of.
toKet[emph[vec]_,emph[bases]_]: If emph[bases] is a list of names of valid bases, then for each subspace corresponding basis from emph[bases] is used to form final Ket. Number of subspaces is deduced from number of bases in emph[bases].";


SyntaxInformation[toKet]={"ArgumentsPattern"->{__}};


toKet::invbas="Invalid basis ``.";
toKet::invbasspac="Invalid specified bases ``";
toKet::invnum="Invalid number `` of subspaces specified.";
toKet::notdiv="Length `1` of input vector is not consistent with given number of subspaces `2`.";
(*toKet::notmult="Length `1` of input vector is not equal to length of specified basis `2` taken to the power of given number of subspaces `3`.";*)
toKet::notprod="Lenght `1` of input vector is not equal to product `2` of lengths `3` of specified bases.";
toKet::moreinfbas="Not unique assignment of infinite bases. Only finite bases with at most one infinite basis, or only infinite bases with equal number of subspace dimensions are supported.";


SetAttributes[toKet,HoldRest];


toKet[{},___]=0;
toKet[vec_List]:=toKet[vec,"Integral",1]


toKet[vec_List,basis:(_String|{Ket[_]..}),num_:1]:=Module[{len=Length[vec](*,locbas,lenbas*)},
		If[NonPositive[num]||Not@IntegerQ[num],Message[toKet::invnum,num];Return[]];	
		toKet[vec,Evaluate@Table[basis,num]]
	]


toKet[vec_List,bases_List]:= (*bases should be a list of Strings or lists of Kets*)
	Module[{finalbasis,len=Length[vec]},
		
		finalbasis=checkAndCreateBasis[bases,len,toKet];
		vec . finalbasis
	]


(* ::Subsubsection::Closed:: *)
(*fromKet*)


fromKet::usage=toNiceFormBraKet@"fromKet[emph[expr]_, emph[bas]_:'Identify',emph[span]_:True]: From a linear combination emph[expr] of Kets expressed in some basis emph[bas] creates a corresponding List vector. If emph[bas] is 'Identify' or omitted, the appropriate basis is deduced from emph[expr]. If emph[bas] is given (as a list of Kets), the procedure only checks whether there are non-repeating Kets, it does not check whether they form valid basis. For infinite bases, if emph[span] is set to True, than the resulting basis contains the whole range of values between Min and Max found in the input state. For example, for input Ket[1]+Ket[3] with emph[span] set to False, the basis is {1,3}. When emph[span] is True, the basis is {1,2,3}.";


SyntaxInformation[fromKet]={"ArgumentsPattern"->{__}};


fromKet::notket="Input expression is not a linear combination of Kets.";
fromKet::absent="The input expression contains basis vectors `1` not present in the specified basis `2`.";


fromKet[expr_,bas:("Identify"|{__Ket}):"Identify",span_:True]:=
	Module[{raw,coefs,specs,pos,vec,absent,locexpr,locbas},
	
		(*get Ket specifications*)
		locexpr=parseKetSpecs[expr,fromKet];
		If[locexpr===$Failed,Return[],{locexpr,coefs,specs}=locexpr];
		
		If[Not@DuplicateFreeQ[specs],Message[fromKet::multterm];Return[]];
		If[Length@Union[Length/@specs]>1,Message[fromKet::diffsub];Return[]];
			
		(*get basis vectors for identified/given bases*)
		locbas=createIdentifiedBasis[bas,specs,span,fromKet];
		If[locbas===Null,Return[]];

		(*determine positions of appropriate nonzero elements in the resulting List*)
		pos=Position[locbas,#]&/@specs;
		
		(*if more terms of input expression contain the same Ket, thrown an error*)
		(*this should not happen anyway, since we check it already at the beginning*)
		If[Not@DuplicateFreeQ[Flatten@pos],Message[fromKet::multterm];Return[]];

		(*if the basis does not contain all elements present in expr, throw an error*)
		absent=Flatten@Position[pos,{}];
		If[absent!={},
			absent=specs[[absent]];
			Message[fromKet::absent,absent,Short[locbas]];
			Return[];
		];

		(*create the resulting list and put nonzero values into appropriate positions*)
		vec=ConstantArray[0,{Length[locbas]}];
		vec[[Flatten[pos]]]=coefs;
		{vec,locbas}
	]


(* ::Title::Closed:: *)
(*End of Package*)


(* ::Subsubsection::Closed:: *)
(*End of Private Context*)


End[];


(* ::Subsubsection::Closed:: *)
(*End of Package*)


Print["For information on usage, see Information for any of the following symbols: "<>
	StringJoin[Riffle[ToString/@`Private`listOfSymbols,", "]]];
EndPackage[];

ToString/@KetsBras`Private`listOfSymbols
