nb={"PlaneWave.nb"}

UsingFrontEnd[
    Print["Generating plots"];
    Table[Print[i]; NotebookEvaluate["D:/Jose/MEGA/Research/Superradiance/"<>i, InsertResults -> True],{i,nb}];
]

Quit[];