(* ::Package:: *)

(* ::Section:: *)
(*Package*)


BeginPackage["Superradiance`SWSH`"];


Off[General::munfl];


(* ::Section:: *)
(*Usage*)


MaxAbs::usage="Returns the maximum of the absolute values, i.e. Max[Abs[x],Abs[y]]"


SpinWeightedSphericalHarmonicY::usage = "Returns the solution to the Teukolsky angular equation when a=0"


SpinWeightedSpheroidalHarmonicS::usage = "Returns the solution to the general Teukolsky angular equation"


SpinWeightedSpheroidalEigenvalueE::usage = "Returns the eigenvalue of the general Teukolsky angular equation"


(* ::Section:: *)
(*Private*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Common functions*)


Unprotect[MaxAbs];
Clear[MaxAbs];
MaxAbs[x_,y_]=Max[Abs[x],Abs[y]];
Protect[MaxAbs];


(* ::Subsection:: *)
(*Angular Equation*)


Clear[EqSWSH];
EqSWSH=\!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]\((\((1 - 
\*SuperscriptBox[\(x\), \(2\)])\)\ \*
SuperscriptBox["S", "\[Prime]",
MultilineFunction->None][x])\)\)+((c x)^2-(m+s x)^2/(1-x^2)+s-2 c s x+A) S[x];


(* ::Subsection:: *)
(*Definitions*)


Clear[Rule\[Kappa]pm,Rule\[ScriptH]];
Rule\[Kappa]pm = {kp -> Abs[m + s]/2, km -> Abs[-m + s]/2};
Rule\[ScriptH] = {\[ScriptH][l_] -> ((l^2 - (kp + km)^2)*(l^2 - (kp - km)^2)*(l^2 - s^2))/(2*(l^2 - 1/4)*l^3)};


Clear[SWSHEigenCoef];
SWSHEigenCoef = {
	l+l^2,
	(-2m s^2)/(l (1+l)),
	\[ScriptH][l+1]-\[ScriptH][l]-1,
	(2 \[ScriptH][l]m s^2)/((l-1)l^2 (l+1))-(2 \[ScriptH][l+1]m s^2)/((l+1)^2 l(l+2)),
	m^2 s^4 ((4 \[ScriptH][l+1])/(l^2 (l+1)^4 (l+2)^2)-(4 \[ScriptH][l])/((l-1)^2 (l)^4 (l+1)^2))-((l+2)\[ScriptH][l+1]\[ScriptH][l+2])/(2(l+1)(2l+3))+\[ScriptH][l+1]^2/(2(l+1))+(\[ScriptH][l]\[ScriptH][l+1])/(2l(l+1))-\[ScriptH][l]^2/(2 l)+((l-1)\[ScriptH][l-1]\[ScriptH][l])/(2l(2l-1)),
	m^3 s^6 ((8 \[ScriptH][l])/(l^6 (l+1)^3 (l-1)^3)-(8 \[ScriptH][l+1])/((l)^3 (l+1)^6 (l+2)^3))+m s^2 \[ScriptH][l](-((\[ScriptH][l+1](7 l^2+7l+4))/(l^3 (l+2)(l+1)^3 (l-1)))-(\[ScriptH][l-1](3l-4))/(l^3 (l+1)(2 l-1)(l-2)))+m s^2 (((3l+7)\[ScriptH][l+1]\[ScriptH][l+2])/(l (l+1)^3 (l+3)(2l+3))-(3 \[ScriptH][l+1]^2)/(l (l+1)^3 (l+2))+(3 \[ScriptH][l]^2)/((l-1)(l)^3 (l+1))),
	(16 m^4 s^8)/(l^4 (l+1)^4) (\[ScriptH][l+1]/((l+2)^4 (l+1)^4)-\[ScriptH][l]/(l^4 (l-1)^4))+(4 m^2 s^4)/(l^2 (l+1)^2) (-(((3 l^2+14l+17)\[ScriptH][l+1]\[ScriptH][l+2])/((l+1)^3 (l+2)(l+3)^2 (2l+3)))+(3 \[ScriptH][l+1]^2)/((l+1)^3 (l+2)^2)-(3 \[ScriptH][l]^2)/(l^3 (l-1)^2)+((11 l^4+22 l^3+31l^2+20l+6)\[ScriptH][l]\[ScriptH][l+1])/((l+1)^3 (l+2)(l+3)^2 (2l+3))+((3 l^2-8l+6)\[ScriptH][l]\[ScriptH][l-1])/(l^3 (l-2)^2 (l-1)(2l-1)))+
(\[ScriptH][l+1]\[ScriptH][l+2])/(4(l+1)(2l+3)^2) (((l+3)\[ScriptH][l+3])/3+(l+2)/(l+1) ((l+2)\[ScriptH][l+2]-(7l+10)\[ScriptH][l+1]+((3l^2+2l-3)\[ScriptH][l])/l))+\[ScriptH][l+1]^3/(2(l+1)^2)-\[ScriptH][l]^3/(2l^2)+(\[ScriptH][l]\[ScriptH][l+1])/(4l^2 (l+1)^2) ((2l^2+4l+3)\[ScriptH][l]-(2l^2+1)\[ScriptH][l+1]-((l^2-1)(3l^2+4l-2)\[ScriptH][l-1])/(2l-1)^2)+
(\[ScriptH][l-1]\[ScriptH][l])/(4l^2 (2l-1)^2) ((l-1)(7l-3)\[ScriptH][l]-(l-1)^2 \[ScriptH][l-1]-(l(l-2)\[ScriptH][l-2])/3)
};


(* ::Subsection::Closed:: *)
(*Leaver method*)


(* to complete *)


(* ::Subsection:: *)
(*Spectral method*)


Clear[\[Beta]1,\[Beta]2];
(* \[LeftAngleBracket]\[ScriptS]\[ScriptL]\[ScriptM]|Cos[\[Theta]]|\[ScriptS]\[ScriptJ]\[ScriptM]\[RightAngleBracket] *)
\[Beta]1[j_,l_,s_,m_]=Sqrt[(2 l+1)/(2 j+1)]ClebschGordan[{l,m},{1,0},{j,m}]ClebschGordan[{l,-s},{1,0},{j,-s}]//PiecewiseExpand;
(* \[LeftAngleBracket]\[ScriptS]\[ScriptL]\[ScriptM]|Cos[\[Theta]]^2|\[ScriptS]\[ScriptJ]\[ScriptM]\[RightAngleBracket] *)
\[Beta]2[j_,l_,s_,m_]=KroneckerDelta[l,j]/3+2/3 Sqrt[(2 l+1)/(2 j+1)]ClebschGordan[{l,m},{2,0},{j,m}]ClebschGordan[{l,-s},{2,0},{j,-s}]//PiecewiseExpand;


Clear[SpectralSWSH];
SpectralSWSH[\[ScriptS]_,\[ScriptL]_,\[ScriptM]_,\[ScriptC]_]:=Module[{l0,delta,lf,nC,sp},
	nC=Ceiling[5*Sqrt[Log[Abs[\[ScriptC]]^3+1] Abs[\[ScriptC]]]+14];
	delta=Ceiling[(nC+\[ScriptL]-MaxAbs[\[ScriptM],\[ScriptS]])/2];
	lf=delta+\[ScriptL];
	l0=Max[\[ScriptL]-delta,MaxAbs[\[ScriptM],\[ScriptS]]]-1;
	sp=SparseArray[{
		{i_,i_}:>-(i+l0)(i+l0+1)-2\[ScriptC] \[ScriptS] \[Beta]1[l0+i,l0+i,\[ScriptS],\[ScriptM]]+\[ScriptC]^2 \[Beta]2[l0+i,l0+i,\[ScriptS],\[ScriptM]],
		{i_,j_}/;Abs[j-i]==1:>-2\[ScriptC] \[ScriptS] \[Beta]1[l0+i,l0+j,\[ScriptS],\[ScriptM]]+\[ScriptC]^2 \[Beta]2[l0+i,l0+j,\[ScriptS],\[ScriptM]],
		{i_,j_}/;Abs[j-i]==2:>\[ScriptC]^2 \[Beta]2[l0+i,l0+j,\[ScriptS],\[ScriptM]]},
	{lf-l0,lf-l0}];
	{#1,{Range[l0+1,lf],Sign[#2[[\[ScriptL]-l0]]]#2}\[Transpose]}&@@(SortBy[{-#1,#2}\[Transpose],First][[\[ScriptL]-l0]]&@@Eigensystem[sp])
];


(* ::Subsection:: *)
(*SpinWeightedSphericalHarmonicY\[InvisiblePrefixScriptBase]\[InvisiblePrefixScriptBase]*)


Unprotect[SpinWeightedSphericalHarmonicY];
Clear[SpinWeightedSphericalHarmonicY];


SyntaxInformation[SpinWeightedSphericalHarmonicY]={"ArgumentsPattern" -> {_, _, _, _., _.}};
SetAttributes[SpinWeightedSphericalHarmonicY, {NumericFunction, Listable}];


SpinWeightedSphericalHarmonicY[\[ScriptS]_Integer,\[ScriptL]_Integer,\[ScriptM]_Integer]:=Function[{\[Theta],\[Phi]},Evaluate@SpinWeightedSphericalHarmonicY[\[ScriptS],\[ScriptL],\[ScriptM],\[Theta],\[Phi]]];
SpinWeightedSphericalHarmonicY[\[ScriptS]_Integer,\[ScriptL]_Integer,\[ScriptM]_Integer, \[Theta]_, \[Phi]_]/;(MaxAbs[\[ScriptM],\[ScriptS]]<=\[ScriptL]):=(-1)^\[ScriptM] Sqrt[((\[ScriptL]+\[ScriptM])!(\[ScriptL]-\[ScriptM])!(2\[ScriptL]+1))/(4\[Pi] (\[ScriptL]+\[ScriptS])!(\[ScriptL]-\[ScriptS])!)] Sum[Binomial[\[ScriptL]-\[ScriptS],r] Binomial[\[ScriptL]+\[ScriptS],r+\[ScriptS]-\[ScriptM]](-1)^(\[ScriptL]-r-\[ScriptS])If[(2\[ScriptL]-2r-\[ScriptS]+\[ScriptM])==0, 1, Sin[\[Theta]/2]^(2\[ScriptL]-2r-\[ScriptS]+\[ScriptM])] Cos[\[Theta]/2]^(2r+\[ScriptS]-\[ScriptM]),{r,Max[\[ScriptM]-\[ScriptS],0],Min[\[ScriptL]-\[ScriptS],\[ScriptL]+\[ScriptM]]}]Exp[I \[ScriptM] \[Phi]];
SpinWeightedSphericalHarmonicY[\[ScriptS]_Integer,\[ScriptL]_Integer,\[ScriptM]_Integer, \[Theta]_, 0.]:=SpinWeightedSphericalHarmonicY[\[ScriptS],\[ScriptL],\[ScriptM],\[Theta],0];
SpinWeightedSphericalHarmonicY[0,\[ScriptL]_Integer,\[ScriptM]_Integer,\[Theta]_,\[Phi]_]:=SphericalHarmonicY[\[ScriptL],\[ScriptM],\[Theta],\[Phi]];


Protect[SpinWeightedSphericalHarmonicY];


(* ::Subsection:: *)
(*SpinWeightedSpheroidalHarmonicS*)


Unprotect[SpinWeightedSpheroidalHarmonicS];
Clear[SpinWeightedSpheroidalHarmonicS];


SyntaxInformation[SpinWeightedSpheroidalHarmonicS]={"ArgumentsPattern" -> {_, _, _, _, _., _.}};
SetAttributes[SpinWeightedSpheroidalHarmonicS, {NumericFunction, Listable}];


SpinWeightedSpheroidalHarmonicS[\[ScriptS]_Integer,\[ScriptL]_Integer,\[ScriptM]_Integer, \[ScriptC]_?NumericQ]/;(Max[Abs[\[ScriptM]],Abs[\[ScriptS]]]<=\[ScriptL]):=Function[{\[Theta],\[Phi]},Evaluate@SpinWeightedSpheroidalHarmonicS[\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptC],\[Theta],\[Phi]]];
SpinWeightedSpheroidalHarmonicS[\[ScriptS]_Integer,\[ScriptL]_Integer,\[ScriptM]_Integer,\[ScriptC]_?NumericQ, \[Theta]_, \[Phi]_]/;(Max[Abs[\[ScriptM]],Abs[\[ScriptS]]]<=\[ScriptL]):=With[{coefs=Transpose@Last@SpectralSWSH[\[ScriptS],\[ScriptL],\[ScriptM],N@\[ScriptC]]},
	Chop[coefs[[2]]].Table[SpinWeightedSphericalHarmonicY[\[ScriptS],j,\[ScriptM],\[Theta],\[Phi]],{j,coefs[[1]]}]//Expand
];


Protect[SpinWeightedSpheroidalHarmonicS];


(* ::Subsection:: *)
(*SpinWeightedSpheroidalEigenvalueE*)


Unprotect[SpinWeightedSpheroidalEigenvalueE];
Clear[SpinWeightedSpheroidalEigenvalueE];


SyntaxInformation[SpinWeightedSpheroidalEigenvalueE]={"ArgumentsPattern" -> {_, _, _, _}};
SetAttributes[SpinWeightedSpheroidalEigenvalueE, {NumericFunction, Listable}];


SpinWeightedSpheroidalEigenvalueE[\[ScriptS]_Integer,\[ScriptL]_Integer?NonNegative,\[ScriptM]_Integer,\[ScriptC]_Real?Negative]:=SpinWeightedSpheroidalEigenvalueE[\[ScriptS],\[ScriptL],-\[ScriptM],-\[ScriptC]];
SpinWeightedSpheroidalEigenvalueE[\[ScriptS]_Integer?Negative,\[ScriptL]_Integer?NonNegative,\[ScriptM]_Integer,\[ScriptC]_]:=SpinWeightedSpheroidalEigenvalueE[-\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptC]];
SpinWeightedSpheroidalEigenvalueE[\[ScriptS]_Integer,\[ScriptL]_Integer?NonNegative,\[ScriptM]_Integer,(0|0.)]:=\[ScriptL](\[ScriptL]+1)/;\[ScriptL]>=MaxAbs[\[ScriptM],\[ScriptS]];
SpinWeightedSpheroidalEigenvalueE[\[ScriptS]_Integer,\[ScriptL]_Integer?NonNegative,\[ScriptM]_Integer,\[ScriptC]_?NumericQ]/;\[ScriptL]>=MaxAbs[\[ScriptM],\[ScriptS]]:=First[SpectralSWSH[\[ScriptS],\[ScriptL],\[ScriptM],N@\[ScriptC]]];
(*\[ScriptCapitalE][\[ScriptS]_Integer,\[ScriptL]_Integer?NonNegative,\[ScriptM]_Integer,\[ScriptC]_Real]/;\[ScriptL]\[GreaterEqual]MaxAbs[\[ScriptM],\[ScriptS]]:=(Simplify[SWSHEigenCoef//.Rule\[ScriptH]\[Union]Rule\[Kappa]pm\[Union]{s\[Rule]\[ScriptS],m\[Rule]\[ScriptM]}]/.l\[Rule]\[ScriptL]).Table[\[ScriptC]^(i-1),{i,Length@SWSHEigenCoef}];*)


Protect[SpinWeightedSpheroidalEigenvalueE];


(* ::Section::Closed:: *)
(*End*)


End[];


EndPackage[];
