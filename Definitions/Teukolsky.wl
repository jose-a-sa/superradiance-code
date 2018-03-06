(* ::Package:: *)

SetDirectory@NotebookDirectory[];
Get["SWSH.wl"]


(* ::Section:: *)
(*Parameters*)


Clear[\[CapitalDelta],\[CapitalSigma],\[Rho],\[ScriptCapitalK],\[ScriptCapitalQ],Rule\[ScriptCapitalK]Radial,EqTeukolskyRadial\[ScriptCapitalK],EqTeukolsky,RuleParams]


\[CapitalDelta][r_]=r^2-2 M r+a^2;
\[CapitalSigma][r_,\[Theta]_]=r^2+a^2 Cos[\[Theta]]^2;
\[Rho][r_,\[Theta]_]:=r+I a Cos[\[Theta]];
\[ScriptCapitalK][r_]=(r^2+a^2) \[Omega]-a m;
\[ScriptCapitalQ][\[Theta]_]=a \[Omega] Sin[\[Theta]]-m Csc[\[Theta]];


Rule\[ScriptCapitalK]Radial={\[Kappa]->Collect[Expand[\[ScriptCapitalK][rp+rp x]]/rp/. {c_ a^2+c_ rp^2->c 2 M rp}/. {a->2 M \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\),\[Omega]->\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)/rp},M,Factor]/.{\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)-m \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\)->(\[Chi] rp)/(2M)}};


EqTeukolskyRadial\[ScriptCapitalK]=(x(x+\[Tau]))^(-s) \!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]\((
\*SuperscriptBox[\((x \((x + \[Tau])\))\), \(s + 1\)] \(R'\)[x])\)\)+((\[Kappa]^2-I s(2x+\[Tau])\[Kappa])/(x(x+\[Tau]))-\[Lambda]+4I s \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)(1+x))R[x];
EqTeukolsky=EqTeukolskyRadial\[ScriptCapitalK]/.Rule\[ScriptCapitalK]Radial;


RuleRHorizon={R->Function[x,x^(-s-I \[Chi]/\[Tau]) f[x]]};
EquationF=PowerExpand@Simplify[x^(s+I \[Chi]/\[Tau]) x (x+\[Tau]) (EqTeukolsky/. RuleRHorizon)];


RuleParams={
rp->1+Sqrt[1-\[ScriptCapitalJ]^2], \[Tau]->(2 Sqrt[1-\[ScriptCapitalJ]^2])/(1+Sqrt[1-\[ScriptCapitalJ]^2]), \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\)->\[ScriptCapitalJ]/2, \[Chi]->(2-\[Tau])(\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)-m \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\)),
c->\[ScriptCapitalJ] \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)/rp, \[ScriptCapitalE]\[ScriptV]->\[ScriptCapitalE][s,l,m,c], 
\[Xi]->c^2-2m c+\[ScriptCapitalE]\[ScriptV], 
\[Lambda]->\[Xi]-s(s+1),
\[ScriptCapitalB]->Sqrt[\[Xi]^2-4c^2+4m c],
\[ScriptCapitalC]->Sqrt[(\[Xi]^2-4c^2+4m c)((\[Xi]-2)^2+36c m -36 c^2)+(2\[Xi]-1)(96c^2-48m c)-(12 c)^2]+12 I \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)/rp
};


Clear[ReplaceParams]
ReplaceParams[\[ScriptJ]_,\[ScriptS]_,\[ScriptL]_,\[ScriptM]_]=#1//. RuleParams\[Union]{s->\[ScriptS],l->\[ScriptL],m->\[ScriptM],\[ScriptCapitalJ]->\[ScriptJ]}&;
ReplaceParams[\[ScriptJ]_,\[ScriptS]_,\[ScriptL]_,\[ScriptM]_,\[ScriptW]_]=#1//.RuleParams\[Union] {s->\[ScriptS],l->\[ScriptL],m->\[ScriptM],\[ScriptCapitalJ]->\[ScriptJ],\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)->\[ScriptW]}&;


(* ::Section:: *)
(*Integrator*)


Clear[nCoefH,nCoefInf,RuleFHorizon,RuleRinInf,RuleRoutInf]


(* Coeficients to estimate f and f' close to BH horizon *)
nCoefH=6;
RuleFHorizon={f->Function[x,\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n = 0\), \(nCoefH\)]\(\[ScriptA][n]\ 
\*SuperscriptBox[\((x)\), \(n\)]\)\)]};


(* Coeficients to estimate Ain and Aout at infinity *)
nCoefInf=6;
RuleRinInf={R->Function[x,E^(-I \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x) x^-1 (2 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x)^(-I (2-\[Tau]) \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)) Sum[\[ScriptI][n] x^-n,{n,0,nCoefInf}]]};
RuleRoutInf={R->Function[x,x^(-1-2 s) E^(I \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x) (2 \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\) x)^(+I (2-\[Tau]) \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)) Sum[\[ScriptO][n] x^-n,{n,0,nCoefInf}]]};


(* ::Section:: *)
(*Integrator*)
