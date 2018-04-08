(* ::Package:: *)

(* ::Section::Closed:: *)
(*Package*)


BeginPackage["Superradiance`Teukolsky`",{"Superradiance`SWSH`"}];


(* ::Section:: *)
(*Usage*)


(* ::Subsection:: *)
(*ReplaceParams*)


ReplaceParams::usage = "";


(* ::Subsection:: *)
(*IncreasePrecision*)


IncreasePrecision::usage = "";


(* ::Subsection:: *)
(*SolveMode*)


SolveMode::usage = "";
SolveMode::solvererr = "Solver option value \"`1`\" is not valid. Using \"Both\" solver.";
SolveMode::parallelerr = "Parallelize option value \"`1`\" is not valid. Using \"ParallelTable\" as default.";


(* ::Subsection:: *)
(*FactorZFormat*)


FactorZFormat::usage = "";
FactorZFormat::solvererr = "Solver option value \"`1`\" is not valid. Using \"Both\" solver formatter.";


(* ::Subsection:: *)
(*PhaseDeltaFormat*)


PhaseDeltaFormat::usage = "";
PhaseDeltaFormat::solvererr = "Solver option value \"`1`\" is not valid. Using \"Both\" solver formatter."


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
ReplaceParams[\[ScriptJ]_,\[ScriptS]_,\[ScriptL]_,\[ScriptM]_]=(#1//. RuleParameters\[Union]{s->\[ScriptS],l->\[ScriptL],m->\[ScriptM],\[ScriptCapitalJ]->\[ScriptJ]})&;
ReplaceParams[\[ScriptJ]_,\[ScriptS]_,\[ScriptL]_,\[ScriptM]_,\[ScriptW]_]=(#1//.RuleParameters\[Union]{s->\[ScriptS],l->\[ScriptL],m->\[ScriptM],\[ScriptCapitalJ]->\[ScriptJ],\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)->\[ScriptW]})&;
Protect[ReplaceParams];


(* ::Subsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
(*Increase precision*)


Unprotect[IncreasePrecision];
Clear[IncreasePrecision];
IncreasePrecision=Sequence[PrecisionGoal->12,AccuracyGoal->70,MaxSteps->10^8];
Protect[IncreasePrecision];


(* ::Subsubsection:: *)
(*Handle methods*)


Unprotect[SolveMode];
Clear[SolveMode];
Options[SolveMode]={"Solver"->Automatic,"Parallelize"->True,"Verbose"->False};


SolveMode[\[ScriptJ]s:({__?NumberQ}|_?NumberQ),\[ScriptS]_?IntegerQ,\[ScriptL]s_:({__?IntegerQ}|_?IntegerQ),\[ScriptM]_?IntegerQ,\[ScriptW]s:({__?NumberQ}|_?NumberQ),opts:OptionsPattern[]]:=
Module[{
solver=Switch[
	OptionValue[{SolveMode,NDSolve},{opts},"Solver"],
	"Both",SolveModeBoth,
	"Single",SolveModeSingle,
	Automatic,SolveModeBoth,
	_,Message[SolveMode::solvererr,OptionValue[{SolveMode,NDSolve},{opts},"Solver"]];SolveModeBoth
],
TableF=If[OptionValue[{SolveMode,NDSolve},{opts},"Parallelize"]!=False,ParallelTable,Table],
\[ScriptW]list=Flatten[{\[ScriptW]s}],
\[ScriptL]list=Flatten[{\[ScriptL]s}],
\[ScriptJ]list=DeleteCases[0|0.]@Flatten[{\[ScriptJ]s}],
len
},
	len=Length[\[ScriptL]list]*Length@DeleteCases[\[ScriptW]list,0|0.|0.5*\[ScriptM]*#|\[ScriptM]*#/2]&/@\[ScriptJ]list//Total;
	If[len==1,solver[\[ScriptJ]list[[1]],\[ScriptS],\[ScriptL]list[[1]],\[ScriptM],First@DeleteCases[0|0.|0.5*\[ScriptM]*\[ScriptJ]list[[1]]|\[ScriptM]*\[ScriptJ]list[[1]]/2]@\[ScriptW]list,opts],
	TableF[solver[\[ScriptJ],\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptW],opts],{\[ScriptL],\[ScriptL]list},{\[ScriptJ],\[ScriptJ]list},{\[ScriptW],DeleteCases[0|0.|0.5*\[ScriptM]*\[ScriptJ]|\[ScriptM]*\[ScriptJ]/2]@\[ScriptW]list}]//FlattenAt[#,Position[#,_?(Depth[#]>2&),Infinity]]&
	]
];


Protect[SolveMode];


(* ::Subsubsection::Closed:: *)
(*Method using both equations*)


Unprotect[SolveModeBoth];
Clear[SolveModeBoth];


SolveModeBoth[\[ScriptJ]_?NumberQ,\[ScriptS]_?IntegerQ,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,opts:OptionsPattern[]]:=
Module[{eqF,f0,fp0,coefInInf,coefOutInf,in,out,ev,x0,xINF,l0,res,time=AbsoluteTime[]},
	x0=10.^(-5);
	xINF=2 \[Pi] 22.(1+\[ScriptL]/4)/Abs[\[ScriptW]];
	ev=SpinWeightedSpheroidalE[\[ScriptS],\[ScriptL],\[ScriptM],(\[ScriptJ] \[ScriptW])/(1+Sqrt[1-\[ScriptJ]^2])];
	eqF=ReplaceParams[\[ScriptJ],\[ScriptS],l0,\[ScriptM],\[ScriptW]][Equation\[ScriptCapitalF]];
	{f0,fp0}={\[ScriptCapitalF][x0],\[ScriptCapitalF]'[x0]}/. Rule\[ScriptCapitalF]Horizon/. First@Solve[CoefficientList[eqF/. Rule\[ScriptCapitalF]Horizon,x][[2;;nCoefH+1]]==0,Evaluate@Table[\[ScriptA][n],{n,1,nCoefH}]];
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
	res={\[ScriptJ],\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptW],in,out}/. ReplaceParams[\[ScriptJ],\[ScriptS],l0,\[ScriptM],\[ScriptW]][{\[ScriptCapitalR]Inf->\[ScriptCapitalR][xINF],\[ScriptCapitalR]pInf->Derivative[1][\[ScriptCapitalR]][xINF]}/. Rule\[ScriptCapitalR]Horizon]/. First@NDSolve[
		{eqF==0,f0==\[ScriptCapitalF][x0],fp0==Derivative[1][\[ScriptCapitalF]][x0]}/. {SpinWeightedSpheroidalE[__]->ev,\[ScriptA][0]->1},
		\[ScriptCapitalF],{x,x0,xINF},
		Sequence@@FilterRules[{opts},Options[NDSolve]]
	];
	If[OptionValue[{SolveMode,NDSolve},{opts},"Verbose"]==True,Print["\[ScriptCapitalJ]=",\[ScriptJ],", \[ScriptL]=", \[ScriptL],", \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)=", \[ScriptW]," (", Round[AbsoluteTime[]-time,0.01]," sec)"]];
	Return[res]
];


Protect[SolveModeBoth];


(* ::Subsubsection::Closed:: *)
(*Method using single equation*)


Unprotect[SolveModeSingle];
Clear[SolveModeSingle];
SolveModeSingle[\[ScriptJ]_?NumberQ,\[ScriptS]_?IntegerQ,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,opts:OptionsPattern[]]:=
Module[{x0,xINF,eqF,f0,fp0,fINF,ev,l0,res,time=AbsoluteTime[]},
	x0=10^-5.;
	xINF=2 \[Pi]/Abs[\[ScriptW]]*50.;
	ev=SpinWeightedSpheroidalE[\[ScriptS],\[ScriptL],\[ScriptM],(\[ScriptJ] \[ScriptW])/(1+Sqrt[1-\[ScriptJ]^2])];
	{eqF,fINF}={Equation\[ScriptCapitalF],\[ScriptCapitalF][xINF]E^(I(Sign[\[ScriptS]]\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) (xINF+(2-\[Tau])Log[xINF])-\[Chi]/\[Tau] Log[xINF]))}//ReplaceParams[\[ScriptJ],\[ScriptS],l0,\[ScriptM],\[ScriptW]];
	{f0,fp0}={\[ScriptCapitalF][x0],\[ScriptCapitalF]'[x0]}/.Rule\[ScriptCapitalF]Horizon/.First@Solve[
		CoefficientList[eqF/.Rule\[ScriptCapitalF]Horizon,x][[2;;nCoefH+1]]==0,
		Evaluate@Table[\[ScriptA][n],{n,1,nCoefH}]
	];
	res={\[ScriptJ],\[ScriptS],\[ScriptL],\[ScriptM],\[ScriptW],fINF}/.First@NDSolve[
		{eqF==0,f0==\[ScriptCapitalF][x0],fp0==\[ScriptCapitalF]'[x0]}/.{SpinWeightedSpheroidalE[__]->ev,\[ScriptA][0]->1},
		\[ScriptCapitalF],{x,x0,xINF},
		Sequence@@FilterRules[{opts}, Options[NDSolve]]
	];
	If[OptionValue[{SolveMode,NDSolve},{opts},"Verbose"]==True,Print["\[ScriptCapitalJ]=",\[ScriptJ],", \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)=", \[ScriptW]," (", Round[AbsoluteTime[]-time,0.01]," sec)"]];
	Return[res]
];
Protect[SolveModeSingle];


(* ::Subsection:: *)
(*Amplification*)


(* ::Subsubsection::Closed:: *)
(*Handle methods*)


Unprotect[FactorZFormat];
Clear[FactorZFormat];
Options[FactorZFormat]={"Solver"->Automatic};


FactorZFormat[x__,opts:OptionsPattern[]]:=Switch[
	OptionValue[{FactorZFormat},{opts},"Solver"],
	"Both",FactorZFormatBoth[x],
	"Single",FactorZFormatSingle[x],
	Automatic,FactorZFormatBoth[x],
	_,Message[FactorZFormat::solverund,OptionValue[{FactorZFormat},{opts},"Solver"]];FactorZFormatBoth[x]]


Protect[FactorZFormat];


(* ::Subsubsection::Closed:: *)
(*Z factor for Both method*)


Unprotect[FactorZFormatBoth];
Clear[FactorZFormatBoth];
FactorZFormatBoth[{x__}]:=FactorZFormatBoth[x];


FactorZFormatBoth[\[ScriptJ]_?NumberQ,1,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Yin_?NumberQ,Yout_?NumberQ]:=
	ReplaceParams[\[ScriptJ],1,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],1,\[ScriptL],\[ScriptM],\[ScriptW],-((\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) \[Tau]^2)/(\[Chi] Abs[Yin]^2)),-(1/(1+(16 \[Chi] \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^3 Abs[Yout]^2)/(\[Tau]^2 \[ScriptCapitalB]^2))),((16 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^4) Abs[Yout/Yin]^2)/\[ScriptCapitalB]^2-1}];


FactorZFormatBoth[\[ScriptJ]_?NumberQ,-1,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Zin_?NumberQ,Zout_?NumberQ]:=
	ReplaceParams[\[ScriptJ],-1,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],-1,\[ScriptL],\[ScriptM],\[ScriptW],-((\[Chi] (\[Tau]^2+4 \[Chi]^2))/(4 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^3 \[Tau]^2 Abs[Zin]^2)),-(1/(1+(\[ScriptCapitalB]^2 \[Tau]^2 Abs[Zout]^2)/(4 \[Chi] \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) (\[Tau]^2+4 \[Chi]^2)))),(\[ScriptCapitalB]^2 Abs[Zout/Zin]^2)/(16 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^4)-1}];


FactorZFormatBoth[\[ScriptJ]_?NumberQ,2,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Yin_?NumberQ,Yout_?NumberQ]:=
	ReplaceParams[\[ScriptJ],2,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],2,\[ScriptL],\[ScriptM],\[ScriptW],-((4 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^3 \[Tau]^4)/(\[Chi] (\[Tau]^2+4 \[Chi]^2) Abs[Yin]^2)),-(1/(1+(64 \[Chi] (\[Tau]^2+4 \[Chi]^2) \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^5 Abs[Yout]^2)/(Abs[\[ScriptCapitalC]]^2 \[Tau]^4))),((256 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^8) Abs[Yout/Yin]^2)/Abs[\[ScriptCapitalC]]^2-1}];


FactorZFormatBoth[\[ScriptJ]_?NumberQ,-2,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Zin_?NumberQ,Zout_?NumberQ]:=
	ReplaceParams[\[ScriptJ],-2,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],-2,\[ScriptL],\[ScriptM],\[ScriptW],-((\[Chi] (\[Tau]^2+\[Chi]^2) (\[Tau]^2+4 \[Chi]^2))/(4 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^5 \[Tau]^4 Abs[Zin]^2)),-(1/(1+(Abs[\[ScriptCapitalC]]^2 \[Tau]^4 Abs[Zout]^2)/(64 \[Chi] (\[Tau]^2+\[Chi]^2) (\[Tau]^2+4 \[Chi]^2) \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^3))),(Abs[\[ScriptCapitalC]]^2 Abs[Zout/Zin]^2)/(256 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)^8)-1}];


Protect[FactorZFormatBoth];


(* ::Subsubsection::Closed:: *)
(*Z factor for Single method*)


Unprotect[FactorZFormatSingle];
Clear[FactorZFormatSingle];
FactorZFormatSingle[{x__}]:=FactorZFormatSingle[x];


FactorZFormatSingle[\[ScriptJ]_?NumberQ,-1|1,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Yin_?NumberQ,Zout_?NumberQ]:=
	ReplaceParams[\[ScriptJ],-1,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],1,\[ScriptL],\[ScriptM],\[ScriptW],-((\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) \[Tau]^2)/(\[Chi] Abs[Yin]^2)),-(1/(1+((\[ScriptCapitalB]^2 \[Tau]^2 Abs[Zout]^2)/(4 \[Chi] \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)(\[Tau]^2+ 4\[Chi]^2))) )),(\[ScriptCapitalB]^2 \[Tau]^4)/(4 (\[Chi]^2) (\[Tau]^2+4\[Chi]^2) ) Abs[Zout/Yin]^2-1}];


Protect[FactorZFormatSingle];


(* ::Subsection:: *)
(*Phase Delta*)


(* ::Subsubsection:: *)
(*Handle methods*)


Unprotect[PhaseDeltaFormat];
Clear[PhaseDeltaFormat];
Options[PhaseDeltaFormat]={"Solver"->Automatic};


PhaseDeltaFormat[x__,opts:OptionsPattern[]]:=Switch[
	OptionValue[{PhaseDeltaFormat},{opts},"Solver"],
	"Both",PhaseDeltaFormatBoth[x],
	Automatic,PhaseDeltaFormatBoth[x],
	_,Message[PhaseDeltaFormat::solverund,OptionValue[{PhaseDeltaFormat},{opts},"Solver"]];PhaseDeltaFormatBoth[x]]


Protect[PhaseDeltaFormat];


(* ::Subsubsection:: *)
(*Phase Delta for Both method*)


Unprotect[PhaseDeltaFormatBoth];
Clear[PhaseDeltaFormatBoth];
PhaseDeltaFormatBoth[{x__}]:=PhaseDeltaFormatBoth[x];


PhaseDeltaFormatBoth[\[ScriptJ]_?NumberQ,+1,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Yin_?NumberQ,Yout_?NumberQ]:=
	ReplaceParams[\[ScriptJ],+1,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],+1,\[ScriptL],\[ScriptM],\[ScriptW],Sequence@@ReIm[(-1)^(\[ScriptL]+1) (4 \[ScriptW]^2)/\[ScriptCapitalB]*Yout/Yin]}]


PhaseDeltaFormatBoth[\[ScriptJ]_?NumberQ,-1,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Zin_?NumberQ,Zout_?NumberQ]:=
	ReplaceParams[\[ScriptJ],-1,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],-1,\[ScriptL],\[ScriptM],\[ScriptW],Sequence@@ReIm[(-1)^(\[ScriptL]+1) \[ScriptCapitalB]/(4 \[ScriptW]^2)*Zout/Zin]}]


PhaseDeltaFormatBoth[\[ScriptJ]_?NumberQ,-2,\[ScriptL]_?IntegerQ,\[ScriptM]_?IntegerQ,\[ScriptW]_?NumberQ,Zin_?NumberQ,Zout_?NumberQ]:=
	ReplaceParams[\[ScriptJ],-2,\[ScriptL],\[ScriptM],\[ScriptW]][{\[ScriptJ],-2,\[ScriptL],\[ScriptM],\[ScriptW],Sequence@@ReIm[(-1)^(\[ScriptL]+1) \[ScriptCapitalC]/(16 \[ScriptW]^4)*Zout/Zin],Sequence@@ReIm[(-1)^(\[ScriptL]+1) \[ScriptCapitalC]\[Conjugate]/(16 \[ScriptW]^4)*Zout/Zin]}]


Protect[PhaseDeltaFormatBoth];


(* ::Subsection::Closed:: *)
(*End*)


End[];


EndPackage[];
