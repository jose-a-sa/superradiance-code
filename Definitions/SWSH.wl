(* ::Package:: *)

EqSWSH=\!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]\((\((1 - 
\*SuperscriptBox[\(x\), \(2\)])\)\ \*
SuperscriptBox["S", "\[Prime]",
MultilineFunction->None][x])\)\)+((c x)^2-(m+s x)^2/(1-x^2)+s-2 c s x+A) S[x];


Clear[SpinWeightedSphericalHarmonicY];
SyntaxInformation[SpinWeightedSphericalHarmonicY]={"ArgumentsPattern" -> {_, _, _, _, _, ___}};
SetAttributes[SpinWeightedSphericalHarmonicY, {NumericFunction, Listable}];
SpinWeightedSphericalHarmonicY[\[ScriptS]_Integer,\[ScriptL]_Integer,\[ScriptM]_Integer]:=Function[{\[Theta],\[Phi]},Evaluate@SpinWeightedSphericalHarmonicY[\[ScriptS],\[ScriptL],\[ScriptM],\[Theta],\[Phi]]];
SpinWeightedSphericalHarmonicY[\[ScriptS]_Integer,\[ScriptL]_Integer,\[ScriptM]_Integer, \[Theta]_, \[Phi]_]/;(Max[Abs[\[ScriptM]],Abs[\[ScriptS]]]<=\[ScriptL]):=(-1)^\[ScriptM] Sqrt[((\[ScriptL]+\[ScriptM])!(\[ScriptL]-\[ScriptM])!(2\[ScriptL]+1))/(4\[Pi] (\[ScriptL]+\[ScriptS])!(\[ScriptL]-\[ScriptS])!)] Sum[Binomial[\[ScriptL]-\[ScriptS],r] Binomial[\[ScriptL]+\[ScriptS],r+\[ScriptS]-\[ScriptM]](-1)^(\[ScriptL]-r-\[ScriptS])If[(2\[ScriptL]-2r-\[ScriptS]+\[ScriptM])==0, 1, Sin[\[Theta]/2]^(2\[ScriptL]-2r-\[ScriptS]+\[ScriptM])] Cos[\[Theta]/2]^(2r+\[ScriptS]-\[ScriptM]),{r,Max[\[ScriptM]-\[ScriptS],0],Min[\[ScriptL]-\[ScriptS],\[ScriptL]+\[ScriptM]]}]Exp[I \[ScriptM] \[Phi]];
SpinWeightedSphericalHarmonicY[\[ScriptS]_Integer,\[ScriptL]_Integer,\[ScriptM]_Integer, \[Theta]_, 0.]:=SpinWeightedSphericalHarmonicY[\[ScriptS],\[ScriptL],\[ScriptM],\[Theta],0];
SpinWeightedSphericalHarmonicY[0,\[ScriptL]_Integer,\[ScriptM]_Integer,\[Theta]_,\[Phi]_]:=SphericalHarmonicY[\[ScriptL],\[ScriptM],\[Theta],\[Phi]];


Clear[\[Beta]1,\[Beta]2];

(* \[LeftAngleBracket]\[ScriptS]\[ScriptL]\[ScriptM]|Cos[\[Theta]]|\[ScriptS]\[ScriptJ]\[ScriptM]\[RightAngleBracket] *)
\[Beta]1[j_,l_,s_,m_]=Sqrt[(2 l+1)/(2 j+1)]ClebschGordan[{l,m},{1,0},{j,m}]ClebschGordan[{l,-s},{1,0},{j,-s}]//PiecewiseExpand;

(* \[LeftAngleBracket]\[ScriptS]\[ScriptL]\[ScriptM]|Cos[\[Theta]]^2|\[ScriptS]\[ScriptJ]\[ScriptM]\[RightAngleBracket] *)
\[Beta]2[j_,l_,s_,m_]=KroneckerDelta[l,j]/3+2/3 Sqrt[(2 l+1)/(2 j+1)]ClebschGordan[{l,m},{2,0},{j,m}]ClebschGordan[{l,-s},{2,0},{j,-s}]//PiecewiseExpand;


Clear[SpectralSWSH]
SpectralSWSH[\[ScriptS]_,\[ScriptL]_,\[ScriptM]_,\[ScriptC]_]:=Module[{l0,nMax,nMin,sp},
	l0=Max[Abs[\[ScriptS]],Abs[\[ScriptM]]];
	nMax=Ceiling[3.5 Sqrt[Log[Abs[\[ScriptC]]^2+1]Abs[\[ScriptC]]]+15];
	nMin=Min[nMax,\[ScriptL]-l0];
	sp=SparseArray[{
		{i_,i_}:>-(i+l0)(i+l0-1)-2 \[ScriptC] \[ScriptS] \[Beta]1[l0-1+i,l0-1+i,\[ScriptS],\[ScriptM]]+ \[ScriptC]^2 \[Beta]2[l0-1+i,l0-1+i,\[ScriptS],\[ScriptM]],
		{i_,j_}/;Abs[j-i]==1:>-2 \[ScriptC] \[ScriptS] \[Beta]1[l0-1+i,l0-1+j,\[ScriptS],\[ScriptM]]+ \[ScriptC]^2 \[Beta]2[l0-1+i,l0-1+j,\[ScriptS],\[ScriptM]],
		{i_,j_}/;Abs[j-i]==2:>\[ScriptC]^2 \[Beta]2[l0-1+i,l0-1+j,\[ScriptS],\[ScriptM]]
	},{nMax+nMin+1,nMin+nMax+1}];
	SortBy[{-#1,Sign[First@MaximalBy[#2,Abs]]#2}&@@@Transpose@Eigensystem[sp],Re@*First][[nMin+1]]
];


SpinWeightedSpheroidalHarmonicEigenvalue[\[ScriptS]_Integer, \[ScriptL]_Integer, \[ScriptM]_Integer, \[ScriptC]_?NumericQ]/;(Max[Abs[\[ScriptM]],Abs[\[ScriptS]]]<=\[ScriptL]) := First@SpectralSWSH[\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptC]];


Clear[SpinWeightedSpheroidalHarmonicS];
SetAttributes[SpinWeightedSpheroidalHarmonicS, {NumericFunction, Listable}];
SpinWeightedSpheroidalHarmonicS[\[ScriptS]_Integer,\[ScriptL]_Integer,\[ScriptM]_Integer, \[ScriptC]_?NumericQ]/;(Max[Abs[\[ScriptM]],Abs[\[ScriptS]]]<=\[ScriptL]):=Function[{\[Theta],\[Phi]},Evaluate@SpinWeightedSpheroidalHarmonicS[\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptC],\[Theta],\[Phi]]];
SpinWeightedSpheroidalHarmonicS[\[ScriptS]_Integer,\[ScriptL]_Integer,\[ScriptM]_Integer,\[ScriptC]_?NumericQ, \[Theta]_, \[Phi]_]/;(Max[Abs[\[ScriptM]],Abs[\[ScriptS]]]<=\[ScriptL]):=With[{coef=Last@SpectralSWSH[\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptC]],l0=Max[Abs[\[ScriptS]],Abs[\[ScriptM]]]},
	coef.Table[SpinWeightedSphericalHarmonicY[\[ScriptS],j,\[ScriptM],\[Theta],\[Phi]],{j,l0,l0-1+Length[coef]}]//Expand//Chop
];


Rule\[Kappa]pm = {kp -> Abs[m + s]/2, km -> Abs[-m + s]/2};
Rule\[ScriptH] = {\[ScriptH][l_] -> ((l^2 - (kp + km)^2)*(l^2 - (kp - km)^2)*(l^2 - s^2))/(2*(l^2 - 1/4)*l^3)};

(* \[Alpha][0]a[1]+\[Beta][0]a[0]=0 *)
(* \[Alpha][p]a[p+1]+\[Beta][p]a[p]+\[Gamma][p]a[p-1]=0 *)
SWSHSeriesCoef = {
	\[Alpha][p_] -> -2*(1 + p)*(1 + 2*km + p), 
	\[Beta][p_] -> -A - c^2 + (km + kp + p - s)*(1 + km + kp + p + s) - 2*c*(1 + 2*km + 2*p + s), 
    \[Gamma][p_] -> 2*c*(km + kp + p + s)
};


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


(***** LEAVER METHOD
 
EigenLeaver[\[ScriptS]_Integer, (\[ScriptL]_Integer)?NonNegative, 
     \[ScriptM]_Integer, (\[ScriptC]_Real)?Negative, M_Integer:150] := 
    EigenLeaver[\[ScriptS], \[ScriptL], -\[ScriptM], -\[ScriptC], M]
 
EigenLeaver[(\[ScriptS]_Integer)?Negative, (\[ScriptL]_Integer)?NonNegative, 
     \[ScriptM]_Integer, \[ScriptC]_Real, M_Integer:150] := 
    EigenLeaver[-\[ScriptS], \[ScriptL], \[ScriptM], \[ScriptC], M]

EigenLeaver[\[ScriptS]_Integer, (\[ScriptL]_Integer)?NonNegative, 
      \[ScriptM]_Integer, (0|0.), M_Integer:150] /; 
     \[ScriptL] >= Max[Abs[\[ScriptS]], Abs[\[ScriptM]]] := \[ScriptL](\[ScriptL]+1)
  
EigenLeaver[\[ScriptS]_Integer, (\[ScriptL]_Integer)?NonNegative, 
      \[ScriptM]_Integer, \[ScriptC]_Real, M_Integer:150] /; 
     \[ScriptL] >= Max[Abs[\[ScriptS]], Abs[\[ScriptM]]] := 
    \[ScriptS]*(\[ScriptS] + 1) + A /. 
     Quiet[FindRoot[Fold[\[Beta][#2 - 1] - (\[Alpha][#2 - 1]*\[Gamma][#2])/
            #1 & , 1, Reverse[Range[M]]] /. (LeaverCoef /. Rule\[Kappa]pm /. 
         {m -> \[ScriptM], l -> \[ScriptL], s -> \[ScriptS], 
          c -> \[ScriptC]}), {A, Table[c^(i - 1), {i, Length[EigenCoef]}] . 
          Simplify[EigenCoef /. Rule\[Kappa]pm /. {m -> \[ScriptM], 
             s -> \[ScriptS]}] /. {l -> \[ScriptL], c -> \[ScriptC]}},Method->"Secant",WorkingPrecision->Max[MachinePrecision,Precision[\[ScriptC]]],AccuracyGoal->Max[MachinePrecision,Precision[\[ScriptC]]]-2]]
             
******)
