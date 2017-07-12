$env:Path += ";C:\Program Files\Wolfram Research\Mathematica\11.1"

Write-Host "Generating plots (evaluating notebooks)"
wolframscript.exe -file autogenPlots.wl

Write-Host "Generating front cover"
cd Thesis/Front
xelatex.exe -interaction=nonstopmode -file-line-error 'main.tex'

Write-Host "Generating Thesis"
cd ..
latexmk.exe -synctex=1 -interaction=nonstopmode -file-line-error -pdf 'main.tex'

cd ..