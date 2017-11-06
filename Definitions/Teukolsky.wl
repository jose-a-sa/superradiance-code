(* ::Package:: *)

\[CapitalDelta][r_]=r^2-2 M r+a^2;
\[CapitalSigma][r_,\[Theta]_]=r^2+a^2 Cos[\[Theta]]^2;
\[Rho][r_,\[Theta]_]:=r+I a Cos[\[Theta]];
\[ScriptCapitalK][r_]=(r^2+a^2) \[Omega]-a m;
\[ScriptCapitalQ][\[Theta]_]=a \[Omega] Sin[\[Theta]]-m Csc[\[Theta]];


RuleKRadial={\[Kappa]->Collect[Expand[\[ScriptCapitalK][rp+rp x]]/rp/. {c_ a^2+c_ rp^2->c 2 M rp}/. {a->2 M \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\),\[Omega]->\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)/rp},M,Factor]/.{\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)-m \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\)->(\[Chi] rp)/(2M)}};


EqTeukolskyRadial=(x(x+\[Tau]))^-s \!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]\((
\*SuperscriptBox[\((x \((x + \[Tau])\))\), \(s + 1\)] \(R'\)[x])\)\)+((\[Kappa]^2-I s(2x+\[Tau])\[Kappa])/(x(x+\[Tau]))-\[Lambda]+4I s \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)(1+x))R[x];
