nb={"PlaneWave.nb"}

UsingFrontEnd[
    Table[Print[i]; NotebookEvaluate["D:/Jose/MEGA/Research/Superradiance/"<>i, InsertResults -> True],{i,nb}];
]

Quit[];