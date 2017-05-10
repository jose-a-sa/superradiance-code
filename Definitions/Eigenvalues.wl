\[ScriptH][l_] := ((l^2 - (kp + km)^2)*(l^2 - (kp - km)^2)*(l^2 - s^2))/
     (2*(l^2 - 1/4)*l^3)
 
LeaverCoef = {\[Alpha][p_] -> -2*(1 + p)*(1 + 2*km + p), 
     \[Beta][p_] -> -A - c^2 + (km + kp + p - s)*(1 + km + kp + p + s) - 
       2*c*(1 + 2*km + 2*p + s), \[Gamma][p_] -> 2*c*(km + kp + p + s)}
 
EigenCoef = {l + l^2 - s*(1 + s), (-2*m*s^2)/(l*(1 + l)), 
     -1 - ((-(-km + kp)^2 + l^2)*(-(km + kp)^2 + l^2)*(l^2 - s^2))/
       (2*l^3*(-1/4 + l^2)) + ((-(-km + kp)^2 + (1 + l)^2)*
        (-(km + kp)^2 + (1 + l)^2)*((1 + l)^2 - s^2))/
       (2*(1 + l)^3*(-1/4 + (1 + l)^2)), 
     ((-(-km + kp)^2 + l^2)*(-(km + kp)^2 + l^2)*m*s^2*(l^2 - s^2))/
       ((-1 + l)*l^5*(1 + l)*(-1/4 + l^2)) - 
      ((-(-km + kp)^2 + (1 + l)^2)*(-(km + kp)^2 + (1 + l)^2)*m*s^2*
        ((1 + l)^2 - s^2))/(l*(1 + l)^5*(2 + l)*(-1/4 + (1 + l)^2)), 
     ((-(-km + kp)^2 + (-1 + l)^2)*(-(km + kp)^2 + (-1 + l)^2)*
        (-(-km + kp)^2 + l^2)*(-(km + kp)^2 + l^2)*((-1 + l)^2 - s^2)*
        (l^2 - s^2))/(8*(-1/4 + (-1 + l)^2)*(-1 + l)^2*l^4*(-1 + 2*l)*
        (-1/4 + l^2)) - ((-(-km + kp)^2 + l^2)^2*(-(km + kp)^2 + l^2)^2*
        (l^2 - s^2)^2)/(8*l^7*(-1/4 + l^2)^2) + 
      ((-(-km + kp)^2 + l^2)*(-(km + kp)^2 + l^2)*(-(-km + kp)^2 + (1 + l)^2)*
        (-(km + kp)^2 + (1 + l)^2)*(l^2 - s^2)*((1 + l)^2 - s^2))/
       (8*l^4*(1 + l)^4*(-1/4 + l^2)*(-1/4 + (1 + l)^2)) + 
      ((-(-km + kp)^2 + (1 + l)^2)^2*(-(km + kp)^2 + (1 + l)^2)^2*
        ((1 + l)^2 - s^2)^2)/(8*(1 + l)^7*(-1/4 + (1 + l)^2)^2) - 
      ((-(-km + kp)^2 + (1 + l)^2)*(-(km + kp)^2 + (1 + l)^2)*
        (-(-km + kp)^2 + (2 + l)^2)*(-(km + kp)^2 + (2 + l)^2)*
        ((1 + l)^2 - s^2)*((2 + l)^2 - s^2))/(8*(1 + l)^4*(2 + l)^2*(3 + 2*l)*
        (-1/4 + (1 + l)^2)*(-1/4 + (2 + l)^2)) + 
      m^2*s^4*((-2*(-(-km + kp)^2 + l^2)*(-(km + kp)^2 + l^2)*(l^2 - s^2))/
         ((-1 + l)^2*l^7*(1 + l)^2*(-1/4 + l^2)) + 
        (2*(-(-km + kp)^2 + (1 + l)^2)*(-(km + kp)^2 + (1 + l)^2)*
          ((1 + l)^2 - s^2))/(l^2*(1 + l)^7*(2 + l)^2*(-1/4 + (1 + l)^2))), 
     m^3*s^6*((4*(-(-km + kp)^2 + l^2)*(-(km + kp)^2 + l^2)*(l^2 - s^2))/
         ((-1 + l)^3*l^9*(1 + l)^3*(-1/4 + l^2)) - 
        (4*(-(-km + kp)^2 + (1 + l)^2)*(-(km + kp)^2 + (1 + l)^2)*
          ((1 + l)^2 - s^2))/(l^3*(1 + l)^9*(2 + l)^3*(-1/4 + (1 + l)^2))) + 
      ((-(-km + kp)^2 + l^2)*(-(km + kp)^2 + l^2)*m*s^2*(l^2 - s^2)*
        (-((-(-km + kp)^2 + (-1 + l)^2)*(-(km + kp)^2 + (-1 + l)^2)*
            (-4 + 3*l)*((-1 + l)^2 - s^2))/(2*(-1/4 + (-1 + l)^2)*(-2 + l)*
           (-1 + l)^3*l^3*(1 + l)*(-1 + 2*l)) - 
         ((4 + 7*l + 7*l^2)*(-(-km + kp)^2 + (1 + l)^2)*(-(km + kp)^2 + 
            (1 + l)^2)*((1 + l)^2 - s^2))/(2*(-1 + l)*l^3*(1 + l)^6*(2 + l)*
           (-1/4 + (1 + l)^2))))/(2*l^3*(-1/4 + l^2)) + 
      m*s^2*((3*(-(-km + kp)^2 + l^2)^2*(-(km + kp)^2 + l^2)^2*(l^2 - s^2)^2)/
         (4*(-1 + l)*l^9*(1 + l)*(-1/4 + l^2)^2) - 
        (3*(-(-km + kp)^2 + (1 + l)^2)^2*(-(km + kp)^2 + (1 + l)^2)^2*
          ((1 + l)^2 - s^2)^2)/(4*l*(1 + l)^9*(2 + l)*(-1/4 + (1 + l)^2)^2) + 
        ((7 + 3*l)*(-(-km + kp)^2 + (1 + l)^2)*(-(km + kp)^2 + (1 + l)^2)*
          (-(-km + kp)^2 + (2 + l)^2)*(-(km + kp)^2 + (2 + l)^2)*
          ((1 + l)^2 - s^2)*((2 + l)^2 - s^2))/(4*l*(1 + l)^6*(2 + l)^3*
          (3 + l)*(3 + 2*l)*(-1/4 + (1 + l)^2)*(-1/4 + (2 + l)^2)))}
 
Rule\[Kappa]pm = {kp -> Abs[m + s]/2, km -> Abs[-m + s]/2}
 
EigenLeaver[\[ScriptS]_Integer, (\[ScriptL]_Integer)?NonNegative, 
     \[ScriptM]_Integer, (\[ScriptC]_)?NumberQ, M_Integer:100] := 
    FindRoot[ContinuedFractionK[\[Beta][n]/(\[Gamma][n + 1]*\[Alpha][n + 1]), 
         {n, 0, M}]^(-1) /. (LeaverCoef /. Rule\[Kappa]pm /. 
        {m -> \[ScriptM], l -> \[ScriptL], s -> \[ScriptS], 
         c -> \[ScriptC]}), {A, \[ScriptL]*(\[ScriptL] + 1) - 
        \[ScriptS]*(\[ScriptS] + 1) - ((2*\[ScriptM]*\[ScriptS])*\[ScriptC])/
         (\[ScriptL]*(\[ScriptL] + 1))}] /; \[ScriptL] >= 
      Max[Abs[\[ScriptS]], Abs[\[ScriptM]]]