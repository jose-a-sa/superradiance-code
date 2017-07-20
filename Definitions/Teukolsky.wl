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


Clear@SpinWeightedSphericalHarmonicY;
SyntaxInformation[SpinWeightedSphericalHarmonicY]={"ArgumentsPattern" -> {_, _, _, _, _, ___}};
SetAttributes[SpinWeightedSphericalHarmonicY, {NumericFunction, Listable}];
SpinWeightedSphericalHarmonicY[s_,\[ScriptL]_,m_]:=Function[{\[Theta],\[Phi]},Evaluate@SpinWeightedSphericalHarmonicsY[s,\[ScriptL],m,\[Theta],\[Phi]]];
SpinWeightedSphericalHarmonicY[s_Integer, l_Integer, m_Integer, \[Theta]_, \[Phi]_]:=(-1)^m Sqrt[((l+m)!(l-m)!(2l+1))/(4\[Pi] (l+s)!(l-s)!)] Sum[Binomial[l-s,r] Binomial[l+s,r+s-m] (-1)^(l-r-s) If[(2 l - 2 r - s + m)==0, 1, Sin[\[Theta]/2]^(2 l - 2 r - s + m)] Cos[\[Theta]/2]^(2 r + s - m),{r,Max[m-s,0],Min[l-s,l+m]}]Exp[I m \[Phi]];
SpinWeightedSphericalHarmonicY[s_Integer, l_Integer, m_Integer, \[Theta]_, \[Phi]_]/;(Abs[m]>l)=0;
SpinWeightedSphericalHarmonicY[s_Integer, l_Integer, m_Integer, \[Theta]_, 0.]:=SpinWeightedSphericalHarmonicY[s, l, m, \[Theta], 0];
SpinWeightedSphericalHarmonicY[0, l_, m_, \[Theta]_, \[Phi]_]:=SphericalHarmonicY[l, m, \[Theta], \[Phi]];
