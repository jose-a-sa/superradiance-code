(* ::Package:: *)




(* ::Section:: *)
(*Package*)


BeginPackage["Superradiance`Teukolsky`",{"Superradiance`SWSH`"}];


(* ::Section:: *)
(*Usage*)


ReplaceParams::usage = "";


SolveMode::usage = "";


FactorZFormat::usage = "";


FactorZ::usage = "";


PhaseDeltaFormat::usage = "";


FactorZFormatBoth::usage = "";


PhaseDelta::usage = "";





(* ::Section:: *)
(*Private*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Parameters*)


Clear[RuleParameters]
RuleParameters={
	rp->1+Sqrt[1-\[ScriptCapitalJ]^2],
	\[Tau]->(2 Sqrt[1-\[ScriptCapitalJ]^2])/(1+Sqrt[1-\[ScriptCapitalJ]^2]),
	\!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\)->\[ScriptCapitalJ]/2, 
	\[Chi]->(2-\[Tau])(\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)-m \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\)),
	c->\[ScriptCapitalJ] \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)/rp,
	\[ScriptCapitalE]\[ScriptV]->SpinWeightedSpheroidalE[s,l,m,c], (* NEEDS Superrradiance`SWSH` *) 
	\[Xi]->c^2-2m c+\[ScriptCapitalE]\[ScriptV], 
	\[Lambda]->\[Xi]-s(s+1),
	\[ScriptCapitalB]->Sqrt[\[Xi]^2-4c^2+4m c],
	\[ScriptCapitalC]->Sqrt[(\[Xi]^2-4c^2+4m c)((\[Xi]-2)^2+36c m -36 c^2)+(2\[Xi]-1)(96c^2-48m c)-(12 c)^2]+12 I \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)/rp
};


(* ::Subsection:: *)
(*Functions*)


Clear[\[CapitalDelta],\[CapitalSigma],\[Rho],\[ScriptCapitalK],\[ScriptCapitalQ]];
\[CapitalDelta][r_]=r^2-2 M r+a^2;
\[CapitalSigma][r_,\[Theta]_]=r^2+a^2 Cos[\[Theta]]^2;
\[Rho][r_,\[Theta]_]:=r+I a Cos[\[Theta]];
\[ScriptCapitalK][r_]=(r^2+a^2) \[Omega]-a m;
\[ScriptCapitalQ][\[Theta]_]=a \[Omega] Sin[\[Theta]]-m Csc[\[Theta]];


Unprotect[ReplaceParams];
Clear[ReplaceParams];
ReplaceParams[\[ScriptJ]_,\[ScriptS]_,\[ScriptL]_,\[ScriptM]_]=#1//. RuleParameters\[Union]{s->\[ScriptS],l->\[ScriptL],m->\[ScriptM],\[ScriptCapitalJ]->\[ScriptJ]}&;
ReplaceParams[\[ScriptJ]_,\[ScriptS]_,\[ScriptL]_,\[ScriptM]_,\[ScriptW]_]=#1//.RuleParameters\[Union]{s->\[ScriptS],l->\[ScriptL],m->\[ScriptM],\[ScriptCapitalJ]->\[ScriptJ],\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)->\[ScriptW]}&;
Protect[ReplaceParams];


(* ::Subsection:: *)
(*Equations*)


Clear[EqTeukolskyRadial\[ScriptCapitalK]];
EqTeukolskyRadial\[ScriptCapitalK]=(x(x+\[Tau]))^(-s) \!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]\((
\*SuperscriptBox[\((x \((x + \[Tau])\))\), \(s + 1\)] \(\[ScriptCapitalR]'\)[x])\)\)+((\[Kappa]^2-I s(2x+\[Tau])\[Kappa])/(x(x+\[Tau]))-\[Lambda]+4I s \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)(1+x))\[ScriptCapitalR][x];


Clear[Rule\[ScriptCapitalK]Radial,EqTeukolsky];
Rule\[ScriptCapitalK]Radial={\[Kappa]->Collect[Expand[\[ScriptCapitalK][rp(1+x)]]/rp/. {c_ a^2+c_ rp^2->c 2 M rp}/. {a->2 M \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\),\[Omega]->\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)/rp},M,Factor]/.{\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)-m \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\)->(\[Chi] rp)/(2M)}};
EqTeukolsky=EqTeukolskyRadial\[ScriptCapitalK]/.Rule\[ScriptCapitalK]Radial;


Clear[Rule\[ScriptCapitalR]Horizon,Equation\[ScriptCapitalF]];
Rule\[ScriptCapitalR]Horizon={\[ScriptCapitalR]->Function[x,x^(-s-I \[Chi]/\[Tau]) \[ScriptCapitalF][x]]};
Equation\[ScriptCapitalF]=PowerExpand@Simplify[x^(s+I \[Chi]/\[Tau]) x (x+\[Tau]) (EqTeukolsky/. Rule\[ScriptCapitalR]Horizon)];


(* ::Subsection:: *)
(*Series expansions*)


Clear[nCoefH,Rule\[ScriptCapitalF]Horizon];
nCoefH=6;
Rule\[ScriptCapitalF]Horizon={\[ScriptCapitalF]->Function[x,\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n = 0\), \(nCoefH\)]\(\[ScriptA][n]\ 
\*SuperscriptBox[\((x)\), \(n\)]\)\)]};


(* Coeficients to estimate Ain and Aout at infinity *)
Clear[nCoefInf,Rule\[ScriptCapitalR]inInf,Rule\[ScriptCapitalR]outInf];
nCoefInf=6;
Rule\[ScriptCapitalR]inInf={\[ScriptCapitalR]->Function[x,x^-1 E^(-I \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x) (2 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x)^(-I (2-\[Tau]) \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)) \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n = 0\), \(nCoefInf\)]\(\[ScriptI][n]\ 
\*SuperscriptBox[\(x\), \(-n\)]\)\)]};
Rule\[ScriptCapitalR]outInf={\[ScriptCapitalR]->Function[x,x^(-1-2 s) E^(I \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x) (2 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x)^(+I (2-\[Tau]) \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)) \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n = 0\), \(nCoefInf\)]\(\[ScriptO][n]\ 
\*SuperscriptBox[\(x\), \(-n\)]\)\)]};


(* ::Subsection:: *)
(*Integrator*)


Clear[IncreasePrecision];


Unprotect[SolveMode];
Clear[SolveMode];
Options[SolveMode]={"Solver"->Automatic};
SolveMode[\[ScriptJ]_?NumberQ,\[ScriptS]_?IntegerQ,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,opts:OptionsPattern[]]:=SolveMode[\[ScriptJ],\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptW],OptionValue[{SolveMode,NDSolve},{opts},"Solver"],Sequence@@FilterRules[{opts},Except["Solver"]]]/;0<\[ScriptJ]<1&&\[ScriptL]>=MaxAbs[\[ScriptS],\[ScriptM]]
SolveMode[\[ScriptJ]_?NumberQ,\[ScriptS]_?IntegerQ,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Automatic,opts:OptionsPattern[]]:=SolveMode[\[ScriptJ],\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptW],"Both",opts]/;0<\[ScriptJ]<1&&\[ScriptL]>=MaxAbs[\[ScriptS],\[ScriptM]]


SolveMode[\[ScriptJ]_?NumberQ,\[ScriptS]_?IntegerQ,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,"Both",opts:OptionsPattern[]]/;0<\[ScriptJ]<1&&\[ScriptL]>=MaxAbs[\[ScriptS],\[ScriptM]]:=
Module[{eqF,f0,fp0,coefInInf,coefOutInf,in,out,ev,x0,xINF,l0},
	x0=10^-12.;
	xINF=2 \[Pi] 80./Abs[\[ScriptW]];
	ev=SpinWeightedSpheroidalE[\[ScriptS],\[ScriptL],\[ScriptM],(\[ScriptJ] \[ScriptW])/(1+Sqrt[1-\[ScriptJ]^2])];
	eqF=ReplaceParams[\[ScriptJ],\[ScriptS],l0,\[ScriptM],\[ScriptW]][Equation\[ScriptCapitalF]];
	{f0,fp0}={\[ScriptCapitalF][x0],Derivative[1][\[ScriptCapitalF]][x0]}/. Rule\[ScriptCapitalF]Horizon/. First@Solve[CoefficientList[eqF/. Rule\[ScriptCapitalF]Horizon,x][[2;;nCoefH+1]]==0,Evaluate@Table[\[ScriptA][n],{n,1,nCoefH}]];
	coefInInf=First@Solve[
		(0==Simplify@SeriesCoefficient[ReplaceParams[\[ScriptJ],\[ScriptS],l0,\[ScriptM],\[ScriptW]]@Series[E^(I \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x) (2 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x)^(I \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) (2-\[Tau])) EqTeukolsky/. Rule\[ScriptCapitalR]inInf,{x,\[Infinity],nCoefInf}],#1]&)/@Range[nCoefInf],
		Evaluate@Table[\[ScriptI][n],{n,1,nCoefInf}]
	];
	coefOutInf=First@Solve[
		(0==Simplify@SeriesCoefficient[ReplaceParams[\[ScriptJ],\[ScriptS],l0,\[ScriptM],\[ScriptW]]@Series[x^(2 s) E^(-I \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x) (2 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x)^(-I \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) (2-\[Tau])) EqTeukolsky/. Rule\[ScriptCapitalR]outInf,{x,\[Infinity],nCoefInf}],#1]&)/@Range[nCoefInf],
		Evaluate@Table[\[ScriptO][n],{n,1,nCoefInf}]
	];
	{in,out}=Total@ReplaceParams[\[ScriptJ],\[ScriptS],l0,\[ScriptM],\[ScriptW]][{\[ScriptCapitalR][x]/. Rule\[ScriptCapitalR]inInf/. coefInInf,\[ScriptCapitalR][x]/. Rule\[ScriptCapitalR]outInf/. coefOutInf}]//
		({\[ScriptI][0],\[ScriptO][0]}/. First@Solve[{#1==\[ScriptCapitalR]Inf,\!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]#1\)==\[ScriptCapitalR]pInf}/. {x->xINF,SpinWeightedSpheroidalE[__]->ev},{\[ScriptI][0],\[ScriptO][0]}]&);
	{\[ScriptJ],\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptW],in,out}/. ReplaceParams[\[ScriptJ],\[ScriptS],l0,\[ScriptM],\[ScriptW]][{\[ScriptCapitalR]Inf->\[ScriptCapitalR][xINF],\[ScriptCapitalR]pInf->Derivative[1][\[ScriptCapitalR]][xINF]}/. Rule\[ScriptCapitalR]Horizon]/. First@Echo@NDSolve[
		{eqF==0,f0==\[ScriptCapitalF][x0],fp0==Derivative[1][\[ScriptCapitalF]][x0]}/. {SpinWeightedSpheroidalE[__]->ev,\[ScriptA][0]->1},
		\[ScriptCapitalF],{x,x0,xINF},
		Sequence@@FilterRules[{opts},Options[NDSolve]]
	]
];


SolveMode[\[ScriptJ]_?NumberQ,\[ScriptS]_?IntegerQ,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,"Single",opts:OptionsPattern[]]/;0<\[ScriptJ]<1&&\[ScriptL]>=MaxAbs[\[ScriptS],\[ScriptM]]:=
Module[{x0,xINF,eqF,f0,fp0,fINF,ev,l0},
	x0=10^-12.;
	xINF=2 \[Pi]/Abs[\[ScriptW]]*200.;
	ev=SpinWeightedSpheroidalE[\[ScriptS],\[ScriptL],\[ScriptM],(\[ScriptJ] \[ScriptW])/(1+Sqrt[1-\[ScriptJ]^2])];
	{eqF,fINF}={Equation\[ScriptCapitalF],\[ScriptCapitalF][xINF]E^(I(Sign[\[ScriptS]]\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) (xINF+(2-\[Tau])Log[xINF])-\[Chi]/\[Tau] Log[xINF]))}//ReplaceParams[\[ScriptJ],\[ScriptS],l0,\[ScriptM],\[ScriptW]];
	{f0,fp0}={\[ScriptCapitalF][x0],\[ScriptCapitalF]'[x0]}/.Rule\[ScriptCapitalF]Horizon/.First@Solve[
		CoefficientList[eqF/.Rule\[ScriptCapitalF]Horizon,x][[2;;nCoefH+1]]==0,
		Evaluate@Table[\[ScriptA][n],{n,1,nCoefH}]
	];
	{\[ScriptJ],\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptW],fINF}/.First@NDSolve[
		{eqF==0,f0==\[ScriptCapitalF][x0],fp0==\[ScriptCapitalF]'[x0]}/.{SpinWeightedSpheroidalE[__]->ev,\[ScriptA][0]->1},
		\[ScriptCapitalF],{x,x0,xINF},
		Sequence@@FilterRules[{opts}, Options[NDSolve]]
	]
];


Protect[SolveMode];


(* ::Subsection:: *)
(*Amplification*)


Clear[FactorZFormatSingle];
FactorZFormatSingle[{x__}]:=FactorZFormatSingle[x];


FactorZFormatSingle[\[ScriptJ]_?NumberQ,-1|1,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Yin_?NumericQ,Zout_?NumericQ]:=
	ReplaceParams[\[ScriptJ],-1,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],1,\[ScriptL],\[ScriptW],-((\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) \[Tau]^2)/(\[Chi] Abs[Yin]^2)),-(1/(1+((\[ScriptCapitalB]^2 \[Tau]^2 Abs[Zout]^2)/(4 \[Chi] \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)(\[Tau]^2+ 4\[Chi]^2))) )),(\[ScriptCapitalB]^2 \[Tau]^4)/(4 (\[Chi]^2) (\[Tau]^2+4\[Chi]^2) ) Abs[Zout/Yin]^2-1}];


Clear[FactorZFormatBoth];
FactorZFormatBoth[{x__}]:=FactorZFormatBoth[x];


FactorZFormatBoth[\[ScriptJ]_?NumberQ,1,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Yin_?NumericQ,Yout_?NumericQ]:=
	ReplaceParams[\[ScriptJ],1,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],1,\[ScriptL],\[ScriptW],-((\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) \[Tau]^2)/(\[Chi] Abs[Yin]^2)),-(1/(1+(16 \[Chi] \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^3 Abs[Yout]^2)/(\[Tau]^2 \[ScriptCapitalB]^2))) ,((16 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^4)/ (\[ScriptCapitalB]^2))Abs[Yout/Yin]^2-1}];


FactorZFormatBoth[\[ScriptJ]_?NumberQ,-1,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Zin_?NumericQ,Zout_?NumericQ]:=
	ReplaceParams[\[ScriptJ],-1,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],-1,\[ScriptL],\[ScriptW],-((\[Chi](\[Tau]^2+ 4\[Chi]^2))/(4 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^3 \[Tau]^2 Abs[Zin]^2)),-(1/(1+(\[ScriptCapitalB]^2 \[Tau]^2 Abs[Zout]^2)/(4 \[Chi] \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) (\[Tau]^2+4 \[Chi]^2)))),(\[ScriptCapitalB]^2/(16 (\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^4) ))Abs[Zout/Zin]^2-1}];


FactorZFormatBoth[\[ScriptJ]_?NumberQ,2,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Yin_?NumericQ,Yout_?NumericQ]:=
	ReplaceParams[\[ScriptJ],2,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],2,\[ScriptL],\[ScriptW],-((4 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^3 \[Tau]^4)/(\[Chi] (\[Tau]^2+4 \[Chi]^2) Abs[Yin]^2)),-(1/(1+(64\[Chi] (\[Tau]^2+4 \[Chi]^2)  \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^5 Abs[Yout]^2)/( Abs[\[ScriptCapitalC]]^2 \[Tau]^4))) ,((256\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^8)/Abs[\[ScriptCapitalC]]^2)Abs[Yout/Yin]^2-1}];


FactorZFormatBoth[\[ScriptJ]_?NumberQ,-2,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Zin_?NumericQ,Zout_?NumericQ]:=
	ReplaceParams[\[ScriptJ],-2,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],-2,\[ScriptL],\[ScriptW],-((\[Chi] (\[Tau]^2+\[Chi]^2) (\[Tau]^2+4 \[Chi]^2) )/(4  \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^5 \[Tau]^4 Abs[Zin]^2)),-(1/(1+(Abs[\[ScriptCapitalC]]^2 \[Tau]^4 Abs[Zout]^2)/(64 \[Chi] (\[Tau]^2+\[Chi]^2) (\[Tau]^2+4 \[Chi]^2) \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^3))),( Abs[\[ScriptCapitalC]]^2/(256\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^8))Abs[Zout/Zin]^2-1}];


(* ::Subsection:: *)
(*Phase Delta*)


(* ::Subsection:: *)
(*End*)


End[];


EndPackage[];
