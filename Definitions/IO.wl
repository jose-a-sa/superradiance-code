(* ::Package:: *)

GetZFile[s_Integer, (l_Integer)?NonNegative, m_Integer, diff_String:""] := 
    StringJoin["Data/", StringRiffle[{"Z", s, l, m, diff}/.{""->Nothing}, "_"], ".csv"] /; 
     l >= Max[Abs[s], Abs[m]]
GetZFile[]:=SortBy[FileNames["Z_*",{"Data"}],(Last@StringSplit[#,"_"]&)];


GetZFileBCP[(s_Integer)?NonPositive, (l_Integer)?NonNegative, m_Integer] := 
    StringRiffle[{"Data/", "Z-Brito-Cardoso-Pani/", "sigma_VS_om_a_", "s", 
       -Abs[s], "l", l, "m", m, ".dat"}, ""] /; l >= Max[Abs[s], Abs[m]]
GetZFileBCP[]:=FileNames["sigma_VS*",{"Data/Z-Brito-Cardoso-Pani"}];     


GetSWSHEigenFile[s_Integer, (l_Integer)?NonNegative, m_Integer, diff_String:""] := 
    StringJoin["Data/", "SWSH-Eigenvalues/", StringRiffle[{"SWSH", "EV", s, l, m, diff}/.{""->Nothing}, "_"], ".csv"] /; 
     l >= Max[Abs[s], Abs[m]]
GetSWSHEigenFile[]:=SortBy[FileNames["SWSH_EV*",{"Data\\SWSH-Eigenvalues"}],(Last@StringSplit[#,"_"]&)];


Get\[Phi]File[s_Integer, (l_Integer)?NonNegative, m_Integer, diff_String:""] := 
    StringJoin["Data/", StringRiffle[{"YinZoutCoef", s, l, m, diff}/.{""->Nothing}, "_"], ".csv"] /; 
     l >= Max[Abs[s], Abs[m]]
Get\[Phi]File[]:=SortBy[FileNames["YinZoutCoef_*",{"Data"}],(Last@StringSplit[#,"_"]&)];


Clear[ExportCSV];
ExportCSV[file_,data_,meta_:OptionsPattern[]]:=Module[{other,columns,metalines},
other=StringRiffle[{#1,": ",EngineeringForm@#2,", "},""]&@@@DeleteCases[("label"->_)|("headers"->_)][meta]//"# "<>StringJoin[#]&;
columns=If[FilterRules[meta,"headers"]=={},"",StringRiffle[("headers"/.meta),{"# "," | "," "}]];
metalines=StringRiffle[{"# "<>FileBaseName[file]<>"."<>FileExtension[file],If[DeleteCases[("label"->_)|("headers"->_)][meta]=={},Nothing,other],If[FilterRules[meta,"headers"]=={},Nothing,columns]},"\n"];
Export[file,metalines<>"\n"<>ExportString[data,"CSV"],"Text"]
];


Clear[ImportCSV];
ImportCSV[file_,OptionsPattern[{PrintMetadata->False}]]:=Module[{raw,meta,table},
raw=Import[file,"Text"];
meta=StringTrim@StringJoin@StringCases[raw,StartOfLine~~"#"~~Shortest[__]~~EndOfLine~~"\n"];
table=StringReplace[raw,{StartOfLine~~"#"~~Shortest[___]~~EndOfLine~~"\n"->"","#"~~Shortest[___]~~EndOfLine->""}];
If[OptionValue[PrintMetadata],Print@meta];
ImportString[table]
]
