(* ::Package:: *)

GetZFile[s_Integer, (l_Integer)?NonNegative, m_Integer, diff_String:""] := 
    StringJoin["Data/", StringRiffle[{"Z", s, l, m, diff}/.{""->Nothing}, "_"], ".csv"] /; 
     l >= Max[Abs[s], Abs[m]]
 


GetZFileBCP[(s_Integer)?NonPositive, (l_Integer)?NonNegative, m_Integer] := 
    StringRiffle[{"Data/", "Z-Brito-Cardoso-Pani/", "sigma_VS_om_a_", "s", 
       -Abs[s], "l", l, "m", m, ".dat"}, ""] /; l >= Max[Abs[s], Abs[m]]
       


GetSWSHEigenFile[s_Integer, (l_Integer)?NonNegative, m_Integer, diff_String:""] := 
    StringJoin["Data/", "SWSH-Eigenvalues/", StringRiffle[{"SWSH", "EV", s, l, m, diff}/.{""->Nothing}, "_"], ".csv"] /; 
     l >= Max[Abs[s], Abs[m]]


Get\[Phi]File[s_Integer, (l_Integer)?NonNegative, m_Integer, diff_String:""] := 
    StringJoin["Data/", StringRiffle[{"YinZoutCoef", s, l, m, diff}/.{""->Nothing}, "_"], ".csv"] /; 
     l >= Max[Abs[s], Abs[m]]
