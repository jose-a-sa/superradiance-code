(* ::Package:: *)

\[CapitalDelta][r_]=r^2-2 M r+a^2;
\[CapitalSigma][r_,\[Theta]_]=r^2+a^2 Cos[\[Theta]]^2;
\[Rho][r_,\[Theta]_]:=r+I a Cos[\[Theta]];
\[ScriptCapitalK][r_]=(r^2+a^2) \[Omega]-a m;
\[ScriptCapitalQ][\[Theta]_]=a \[Omega] Sin[\[Theta]]-m Csc[\[Theta]];


RuleKRadial={\[Kappa]->Collect[Expand[\[ScriptCapitalK][rp+rp x]]/rp/. {c_ a^2+c_ rp^2->c 2 M rp}/. {a->2 M \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\),\[Omega]->\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)/rp},M,Factor]/.{\!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)-m \!\(\*OverscriptBox[\(\[CapitalOmega]\), \(_\)]\)->(\[Chi] rp)/(2M)}};


EqRadial=(x(x+\[Tau]))^-s \!\(
\*SubscriptBox[\(\[PartialD]\), \(x\)]\((
\*SuperscriptBox[\((x \((x + \[Tau])\))\), \(s + 1\)] \(R'\)[x])\)\)+((\[Kappa]^2-I s(2x+\[Tau])\[Kappa])/(x(x+\[Tau]))-\[Lambda]+4I s \!\(\*OverscriptBox[\(\[Omega]\), \(_\)]\)(1+x))R[x];


Clear@SpinWeightedSphericalHarmonicsY;
SpinWeightedSphericalHarmonicsY[s_,\[ScriptL]_,m_]:=Function[{\[Theta],\[Phi]},Evaluate@SpinWeightedSphericalHarmonicsY[s,\[ScriptL],m,\[Theta],\[Phi]]];
SpinWeightedSphericalHarmonicsY[s_,l_,m_,\[Theta]_,\[Phi]_]:=(-1)^m Simplify[Sqrt[((l+m)!(l-m)!(2l+1))/((l+s)!(l-s)!4\[Pi])] (Sin[\[Theta]/2])^(2l) \!\(
\*SubsuperscriptBox[\(\[Sum]\), \(r = 0\), \(l - s\)]\((Binomial[l - s, r] Binomial[l + s, r + s - m] 
\*SuperscriptBox[\((\(-1\))\), \(l - r - s\)] 
\*SuperscriptBox[\(E\), \(I\ m\ \[Phi]\)] 
\*SuperscriptBox[\((Cot[
\*FractionBox[\(\[Theta]\), \(2\)]])\), \(2  r + s - m\)])\)\),Assumptions->{\[Phi]\[Element]Reals,\[Theta]\[Element]Reals}];
