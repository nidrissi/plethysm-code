(* ::Package:: *)

(* ::Title:: *)
(*Code for "Plethysm for characters of relative operads and PROPs" \[Dash] packaged code*)


(* ::Author:: *)
(*Najib Idrissi* and Erik Lindell***)


(* ::Affiliation:: *)
(** Universit\[EAcute] Paris Cit\[EAcute] and Sorbonne Universit\[EAcute], CNRS, IMJ-PRG, F-75013 Paris, France.*)
(*** Institut for Matematiske Fag, K\[OSlash]benhavns Universitet, Universitetsparken 5, 2100 K\[OSlash]benhavn \[CapitalOSlash], Denmark.*)


BeginPackage["Lambda`"]


(* ::Section:: *)
(*Public definitions*)


(* ::Subsection:: *)
(*Partitions*)


tr::usage = "tr[\[Lambda]] The transpose of the partition \[Lambda]"


hook::usage = "hook[\[Lambda]] The hook length formula applied to the partition \[Lambda]."


\[ScriptZ]::usage = "\[ScriptZ][\[Lambda]] The coefficient appearing in the scalar product of power sums."


\[Chi]::usage="\[Chi][\[Lambda], \[Mu]] The value of the character indexed by \[Lambda] on permutations of cycle type \[Mu]."


\[HBar]::usage = "The variable used for the grading."


(* ::Subsection:: *)
(*Symmetric functions*)


m::usage = "m[\[Lambda], x] Standard basis element."
e::usage = "e[n, x] Elementary symmetric polynomial."
h::usage = "h[n, x] Complete symmetric polynomial."
p::usage = "p[n, x] Power sum symmetric polynomial."
s::usage = "s[\[Lambda], x] Schur symmetric polynomial."


alt::usage = "alt[\[Alpha], x] The determinant skew-symmetric polynomial."


view::usage = "view[n][f] Projects the symmetric function f to the ring of symmetric polynomials in n variables."


conv::usage = "conv[t][f] Converts the symmetric function f into the basis with head t."


printPoly::usage = "printPoly[s][f] print a polynomial in the s[\[Lambda]] as a sum of irreducible representations"; 


pl::usage=
"pl[f, g, x] computes the one-variable plethysm f \[SmallCircle] g
pl[f, {g, h}, x, y] computes the two-variable plethysm f \[SmallCircle] (g,h)"


adj::usage = "adj[f, g] represent the action of the adjoint of f on g."


reg::usage = "reg[n, x, y] The bicharacter of the regular representation of S_n, in terms of Schur functions."


reg2::usage = "reg2[n, x, y] The bicharacter of the regular representation of S_n, in terms of power sums."


(* ::Subsection:: *)
(*Actual computations*)


\[Omega]::usage = 
  "\[Omega][f] applies the involution \[Omega] (which tensors with the sign representation in every arity) to f . If f=ch[M] then \[Omega][f]=ch[\[Omega][M]], where \[Omega][M][p,q]=M[p,q]\[CircleTimes]sgn[p]\[CircleTimes]sgn[q]."


\[ScriptCapitalF]::usage = "\[ScriptCapitalF][f, x, y] Applies the regrading automorphism."


chQ::usage = "chQ[d, x, y] The character of \[ScriptCapitalQ] in degree d."


chP\[LetterSpace]upto::usage = "chP\[LetterSpace]upto[d, n, x, y] The character of \[ScriptCapitalP] in degree d up to arity n."


chH\[LetterSpace]upto::usage = "chH\[LetterSpace]upto[d, n, x, y] The character of \[ScriptCapitalH] in degree d up to arity n."


chP::usage = "chP[d, m, n, x, y] The characters of \[ScriptCapitalP] in degree d, output arity m, input arity n."


chH::usage = "chP[d, m, n, x, y] The characters of \[ScriptCapitalH] in degree d, output arity m, input arity n."


chQ\[LetterSpace]prime::usage = "chQ\[LetterSpace]prime[d, x, y] The character of \[ScriptCapitalQ]' in degree d."


chP\[LetterSpace]prime::usage = "chP\[LetterSpace]prime[d, x, y] The character of \[ScriptCapitalP]' in degree d."


chH\[LetterSpace]prime::usage = "chH\[LetterSpace]prime[d, x, y] The character of \[ScriptCapitalP]' in degree d."


(* ::Section:: *)
(*Private definitions*)


Begin["`Private`"]


(* ::Subsection:: *)
(*Utilities*)


(* ::Subsubsection:: *)
(*Partitions*)


tr[\[Lambda]_List] := Module[{s = Select[\[Lambda], #1 > 0 & ], i, row, r}, row = Length[s]; Table[r = row; While[s[[row]] <= i, row--]; r, {i, First[s]}]]


hook[\[Lambda]_List] := With[{\[Lambda]tr = tr[\[Lambda]]}, Total[\[Lambda]]!/Product[\[Lambda][[i]] + \[Lambda]tr[[j]] - i - j + 1, {i, Length[\[Lambda]]}, {j, \[Lambda][[i]]}]]


\[ScriptZ][\[Lambda]_]:=Times@@(#1^#2 #2!&)@@@Tally[\[Lambda]]


(* ::Subsection:: *)
(*Monomials*)


gen[\[Alpha]_List, x_] := Product[Subscript[x, i]^\[Alpha][[i]], {i, Length[\[Alpha]]}]


(* ::Subsection:: *)
(*The variable used for the grading*)


SetAttributes[\[HBar], Protected]


coeff[d_Integer][f_] := (-1)^d*Cancel[SeriesCoefficient[f, {\[HBar], 0, d}]]


(* ::Subsection:: *)
(*Generators*)


(* ::Subsubsection:: *)
(*Formatting the generators*)


MakeBoxes[m[\[Lambda]_List, x_Symbol], StandardForm] ^:= TemplateBox[MakeBoxes /@ {\[Lambda], x}, "m", DisplayFunction -> (RowBox[{SubscriptBox["m", #1], "(", #2, ")"}] & )]
MakeBoxes[e[r_Integer, x_Symbol], StandardForm] ^:= TemplateBox[MakeBoxes /@ {r, x}, "e", DisplayFunction -> (RowBox[{SubscriptBox["e", #1], "(", #2, ")"}] & )]
MakeBoxes[h[r_Integer, x_Symbol], StandardForm] ^:= TemplateBox[MakeBoxes /@ {r, x}, "h", DisplayFunction -> (RowBox[{SubscriptBox["h", #1], "(", #2, ")"}] & )]
MakeBoxes[p[r_Integer, x_Symbol], StandardForm] ^:= TemplateBox[MakeBoxes /@ {r, x}, "p", DisplayFunction -> (RowBox[{SubscriptBox["p", #1], "(", #2, ")"}] & )]
MakeBoxes[s[\[Lambda]_List, x_Symbol], StandardForm] ^:= TemplateBox[MakeBoxes /@ {\[Lambda], x}, "s", DisplayFunction -> (RowBox[{SubscriptBox["s", #1], "(", #2, ")"}] & )]


SyntaxInformation[m]={"ArgumentsPattern"->{_,_}};
SyntaxInformation[e]={"ArgumentsPattern"->{_,_}};
SyntaxInformation[h]={"ArgumentsPattern"->{_,_}};
SyntaxInformation[p]={"ArgumentsPattern"->{_,_}};
SyntaxInformation[s]={"ArgumentsPattern"->{_,_}};


(* ::Subsubsection:: *)
(*The "view" function*)


(* ::Text:: *)
(*Projects an element expressed in terms of Subscript[e, r],Subscript[h, r],Subscript[p, r],Subscript[s, \[Lambda]]... onto symmetric functions in n variables*)


(* ::Subsubsubsection:: *)
(*Standard basis*)


m[{},_Symbol]=1;


(* ::Subsubsubsection:: *)
(*Elementary symmetric functions*)


e[r_Integer, _Symbol] /; r < 0 = 0; 


e[0, _Symbol] = 1; 


e[\[Lambda]_List, x_Symbol] := Product[e[i_, x], {i, \[Lambda]}]


(* ::Subsubsubsection:: *)
(*Complete symmetric functions*)


h[r_Integer/;r<0,_Symbol]=0;


h[0, _Symbol] = 1; 


h[\[Lambda]_List, x_Symbol] := Product[h[i, x], {i, \[Lambda]}]


(* ::Subsubsubsection:: *)
(*Power sum*)


p[r_Integer, _Symbol] /; r < 0 = 0; 


p[0, _Symbol] = 1; 


p[\[Lambda]_List,x_Symbol]:=Product[p[i,x],{i,\[Lambda]}]


(* ::Subsubsubsection:: *)
(*Schur functions*)


alt[\[Alpha]_List, x_Symbol] := Det[Table[Subscript[x, i]^\[Alpha][[j]], {i, Length[\[Alpha]]}, {j, Length[\[Alpha]]}]]


s[{}, _Symbol] = 1; 


(* ::Subsubsubsection:: *)
(*The other rules*)


varList[n_Integer,x_Symbol]:=Subscript[x, #]&/@Range[n]


viewRules[n_Integer] := {
	m[\[Lambda]_List, x_Symbol] /; Length[\[Lambda]] > n :> 0,
	m[\[Lambda]_List, x_Symbol] :> Sum[gen[\[Tau], x], {\[Tau], Permutations[PadRight[\[Lambda], n]]}],
	e[r_Integer, x_Symbol] /; r > n :> 0,
	e[r_Integer, x_Symbol] :> SymmetricPolynomial[r, varList[n, x]],
	h[r_Integer, x_Symbol] :> Sum[m[\[Lambda], x], {\[Lambda], IntegerPartitions[r]}], 
    p[r_Integer, x_Symbol] :> PowerSymmetricPolynomial[r, varList[n, x]],
    s[\[Lambda]_List, x_Symbol] /; Length[\[Lambda]] > n :> 0, 
    s[\[Lambda]_List, x_Symbol] :> With[{\[Delta] = Range[n - 1, 0, -1]}, Cancel[alt[PadRight[\[Lambda], n] + \[Delta], x]/alt[\[Delta], x]]]
}


view[n_Integer][f_]:=f//.viewRules[n]


(* ::Subsection:: *)
(*Conversion between bases*)


convRules[m]:={
	e[r_Integer, x_Symbol]:> m[ConstantArray[1, r], x],
	h[r_Integer, x_Symbol]:> Sum[m[\[Lambda], x], {\[Lambda], IntegerPartitions[r]}],
	p[r_Integer, x_Symbol]:> m[{r}, x]
}


convRules[e] := {
	h[r_Integer, x_Symbol] :> Det[Array[e[1 - #1 + #2, x] & , {r, r}]],
	p[r_Integer, x_Symbol] :> Det[Array[If[#1 == 1, #2, 1]*e[1 - #1 + #2, x] & , {r, r}]], 
	s[\[Lambda]_List, x_Symbol] :> With[{\[Lambda]tr = tr[\[Lambda]]}, Det[Array[e[\[Lambda]tr[[#1]] - #1 + #2, x] & , {Length[\[Lambda]tr], Length[\[Lambda]tr]}]]]
}


convRules[h] := {
	e[r_Integer, x_Symbol] :> Det[Array[h[1 - #1 + #2, x] & , {r, r}]], 
	p[r_Integer, x_Symbol] :> (-1)^(r - 1)*Det[Array[If[#1 == 1, 1 - #1 + #2, 1]*h[1 - #1 + #2, x] & , {r, r}]], 
	s[\[Lambda]_List, x_Symbol] :> Det[Array[h[\[Lambda][[#1]] - #1 + #2, x] & , {Length[\[Lambda]], Length[\[Lambda]]}]]
}


convRules[p] := {
	e[1, x_Symbol] :> p[1, x],
	h[1, x_Symbol] :> p[1, x],
	e[r_Integer, x_Symbol] :> Det[Array[p[1 - #1 + #2, x] & , {r, r}] + DiagonalMatrix[Range[r - 1] - 1, -1]]/r!,
	h[r_Integer, x_Symbol] :> Det[Array[p[1 - #1 + #2, x] & , {r, r}] - DiagonalMatrix[Range[r - 1] + 1, -1]]/r!,
	s[\[Lambda]_List, x_Symbol] :> Sum[(\[Chi][\[Lambda], \[Mu]]/\[ScriptZ][\[Mu]])*p[\[Mu], x], {\[Mu], IntegerPartitions[Total[\[Lambda]]]}]
}


conv[t:m | e | h | p][f_] := f //. convRules[t]


(* ::Subsubsection:: *)
(*Schur functions*)


(* ::Text:: *)
(*We will use the Murnaghan\[Dash]Nakayama rule.*)


(* ::Text:: *)
(*The character table of the symmetric group Subscript[\[GothicCapitalS], n] is only included for n<=10 in Mathematica. We use an external GAP program to produce them for arbitrary values of n.*)


(*directory=If[$MachineName=="epsilon","/home/nidrissi/sym","C:\\Users\\najib\\OneDrive\\Travail\\Recherche\\Plethysm"];*)
directory = DirectoryName[$InputFileName]
charTableFile[n_Integer]:=FileNameJoin[{directory,"charTable_"<>ToString[n]<>".wl"}]


ClearAll[charTable]


\[Chi]::miss="File `1` is missing."
\[Chi]::fail="Creating `1` failed."


charTable[n_Integer]/;FileExistsQ[charTableFile[n]]:=charTable[n]=With[{tab=Get[charTableFile[n]]},Append[tab,"Indices"->First/@PositionIndex[tab["Classes"]]]]
charTable[n_Integer]/;ChoiceDialog["Create "<>charTableFile[n]<>" using GAP?"]:=If[Run["wsl gap --nointeract symCharTable.gap -c 'storeSymmetricCharacterTable("<>ToString[n]<>");'"]==0,charTable[n],Message[\[Chi]::fail,charTableFile[n]];$Failed]
charTable[n_Integer]:=(Message[\[Chi]::miss,charTableFile[n]];$Failed)


\[Chi][\[Lambda]_List,\[Mu]_List]/;Total[\[Lambda]]==Total[\[Mu]]:=With[{tab=charTable[Total[\[Lambda]]],\[Lambda]s=ReverseSort[\[Lambda]],\[Mu]s=ReverseSort[\[Mu]]},tab["Table"][[tab["Indices"][\[Lambda]s],tab["Indices"][\[Mu]s]]]]


(* ::Text:: *)
(*To convert to the Schur basis, we use the Murnaghan\[Dash]Nakayama rule. We first convert to the power sum basis (TODO: more efficient method?).*)


(* ::Text:: *)
(*We use the following trick to "merge" back products of power sums:*)


pTmp/:pTmp[\[Lambda]_List,x_Symbol]pTmp[\[Mu]_List,x_Symbol]:=pTmp[Join[\[Lambda],\[Mu]],x]
pTmp/:pTmp[\[Lambda]_List,x_Symbol]^k_Integer:=pTmp[Join@@ConstantArray[\[Lambda],k],x]


conv[s][f_] := ExpandAll[conv[p][f]] /. {p[n_, x_] :> pTmp[{n}, x]} /. 
   {pTmp[\[Mu]_, x_] :> Sum[\[Chi][\[Lambda], \[Mu]]*s[\[Lambda], x], {\[Lambda], IntegerPartitions[Total[\[Mu]]]}]}


(* ::Subsection:: *)
(*Pretty printing*)


(* ::Text:: *)
(*"Prints" a polynomial of Schur functions as a sum of irreducible representations*)


seq[\[Lambda]_] := Row[(ToString[#1]^#2 & ) @@@ Tally[\[Lambda]]]
fmt[sym_, x_, y_][(k_Integer)*(f_)] := fmt[sym, x, y][f]^Row[{"\[CirclePlus]", k}]
fmt[sym_, x_, y_][k_Integer] /; k >1 := Subscript[sym, "\[EmptySet]", "\[EmptySet]"]^Row[{"\[CirclePlus]", k}]
fmt[sym_, x_, y_][1] := Subscript[sym, "\[EmptySet]", "\[EmptySet]"]
fmt[__][0] = 0;
fmt[sym_, x_, y_][s[\[Lambda]_, x_]] := Subscript[sym, seq[\[Lambda]], "\[EmptySet]"]
fmt[sym_, x_, y_][s[\[Mu]_, y_]] := Subscript[sym, "\[EmptySet]", seq[\[Mu]]]
fmt[sym_, x_, y_][s[\[Lambda]_, x_]*s[\[Mu]_, y_]] := Subscript[sym, seq[\[Lambda]], seq[\[Mu]]]


print2[sym_, x_, y_][f_Plus] := fmt[sym, x, y] /@ CirclePlus @@ f
print2[sym_, x_, y_][f_] := fmt[sym, x, y][f]


cmp["\[EmptySet]"] = {0, {}}; 
cmp[Row[l_List]] = {Total[ToExpression /@ l], l}; 
cmp[Subscript[_, l1_, l2_]] := {cmp[l1], cmp[l2]}
cmp[(f_)^_] := cmp[f]
sort[0] = 0; 
sort[f_CirclePlus] := ReverseSortBy[f, cmp]
sort[f_] := f


printPoly[sym_Symbol, x_Symbol, y_Symbol][f_] := sort[print2[sym, x, y][Expand[conv[s][f]]]]


(* ::Subsection:: *)
(*Plethysm*)


pl[f_, g_, x_Symbol] := plHelper[conv[p][f], conv[p][g], x]
pl[f_, {g_, h_}, x_Symbol, y_Symbol] := plHelper[conv[p][f], {conv[p][g], conv[p][h]}, x, y]


plHelper[(\[Alpha]_)?NumericQ, _, __] := \[Alpha]; 
plHelper[sum_Plus, g_, x__] := (plHelper[#1, g, x] & ) /@ sum
plHelper[prod_Times, g_, x__] := (plHelper[#1, g, x] & ) /@ prod
plHelper[(f_)^(k_), g_, x__] := plHelper[f, g, x]^k


plHelper[p[m_Integer, x_], p[n_Integer, x_], x_] := p[m*n, x]
plHelper[p[m_Integer, x_], g_, x_] := FromDigits[Reverse[(plHelper[#1, p[m, x], x] & ) /@ CoefficientList[g, \[HBar]]], \[HBar]^m]


plHelper[p[m_Integer, x_], {p[n_Integer, x_], _}, x_, y_] := p[m*n, x]
plHelper[p[m_Integer, x_], {p[n_Integer, y_], _}, x_, y_] := p[m*n, y]


plHelper[p[m_Integer, x_], {g_, h_}, x_, y_] := FromDigits[Reverse[(plHelper[#1, {p[m, x], p[m, y]}, x, y] & ) /@ CoefficientList[g, \[HBar]]], \[HBar]^m]
plHelper[p[m_Integer, y_], {_, g_}, _, y_] := plHelper[p[m, y], g, y]


(* ::Subsection:: *)
(*Orthogonality*)


adj[f_, g_] := adjHelper[conv[p][f], conv[p][g]]


adjHelper[(\[Alpha]_)?NumericQ, g_] := \[Alpha]*g


adjHelper[f_Plus, g_] := (adjHelper[#1, g] & ) /@ f
adjHelper[f_Times, g_] := Fold[adjHelper[#2, #1] & , g, List @@ f]
adjHelper[(f_)^(k_Integer), g_] := Nest[adjHelper[f, #1] & , g, k]


adjHelper[p[n_, x_], g_] := n*D[g, p[n, x]]


reg[n_, x_, y_] := Sum[s[\[Lambda], x]*s[\[Lambda], y], {\[Lambda], IntegerPartitions[n]}]


reg2[n_, x_, y_] := Sum[(p[\[Lambda], x]*p[\[Lambda], y])/\[ScriptZ][\[Lambda]], {\[Lambda], IntegerPartitions[n]}]


(* ::Subsection:: *)
(*Actual computations*)


\[Omega][f_] := f /. {p[n_Integer, x_Symbol] :> (-1)^(n - 1)*p[n, x], s[\[Lambda]_List, x_Symbol] :> s[tr[\[Lambda]], x], h[n_Integer, x_Symbol] :> e[n, x], e[n_Integer, x_Symbol] :> h[n, x]}


\[ScriptCapitalF][f_, x_Symbol, y_Symbol] := conv[p][f] /. {p[n_Integer, x] :> p[n, x]/(-\[HBar])^n, p[n_Integer, y] :> (-\[HBar])^n*p[n, y]}


chQ[d_Integer, x_Symbol, y_Symbol] := If[d >= 1, h[d, y], 0] + If[d + 1 >= 1, h[d + 1, y]*e[1, x], 0]


chP\[LetterSpace]upto[d_Integer, n_Integer, x_Symbol, y_Symbol] := Expand[conv[s][coeff[d][\[ScriptCapitalF][Sum[pl[h[k, x], {Sum[chQ[l, x, y], {l, 0, d}], 0}, x, y], {k, 0, n}], x, y]]] /. 
    s[\[Lambda]_ /; Total[\[Lambda]] > n, y] :> 0]


chH\[LetterSpace]upto[d_Integer, n_Integer, x_Symbol, y_Symbol] := chH\[LetterSpace]upto[d, n, x, y] = \[Omega][chP\[LetterSpace]upto[d, n, x, y]]


chP[d_Integer, m_Integer, n_Integer, x_Symbol, y_Symbol] := Expand[conv[s][coeff[d][\[ScriptCapitalF][Sum[pl[h[k, x], {Sum[chQ[l, x, y], {l, 0, d}], 0}, x, y], {k, 0, n}], x, y]]]] /. 
   {s[\[Lambda]_ /; Total[\[Lambda]] != n, y] :> 0, s[\[Mu]_ /; Total[\[Mu]] != m, x] :> 0}


chH[d_Integer, m_Integer, n_Integer, x_Symbol, y_Symbol] := chH[d, m, n, x, y] = \[Omega][chP[d, m, n, x, y]]


chQ\[LetterSpace]prime[d_Integer, x_Symbol, y_Symbol] := If[d >= 1, h[d, y], 0] + If[d + 1 >= 2, h[d + 1, y]*h[1, x], 0]


chP\[LetterSpace]prime\[LetterSpace]upto[d_Integer, x_Symbol, y_Symbol] := \[ScriptCapitalF][Sum[pl[h[k, x], {Sum[chQ\[LetterSpace]prime[l, x, y], {l, 0, d}], 0}, x, y], {k, 1, d}], x, y]


chP\[LetterSpace]prime[d_Integer, x_Symbol, y_Symbol] := coeff[d][chP\[LetterSpace]prime\[LetterSpace]upto[d, x, y]]


chH\[LetterSpace]prime[n_Integer, x_Symbol, y_Symbol] := chH\[LetterSpace]prime[n, x, y] = Expand[conv[s][\[Omega][chP\[LetterSpace]prime[n, x, y]]]]


(* ::Section:: *)
(*Fin*)


End[]


EndPackage[]
