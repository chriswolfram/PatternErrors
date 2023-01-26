BeginPackage["ChristopherWolfram`PatternErrors`MatchBranchObject`BranchStyledPattern`"];

BranchStyledPattern

Begin["`Private`"];

Needs["ChristopherWolfram`PatternErrors`"]


matchedColor = RGBColor[0.2,0.5,1];
unmatchedColor = RGBColor[1,0.2,0.15];

(* matchedColor = RGBColor[{92, 152, 97}/255];
unmatchedColor = RGBColor[{129, 43, 38}/255]; *)


BranchStyledPattern[branch_MatchBranchObject /; branch["Type"] === "Atomic"] :=
	Style[HoldForm@@branch["HeldPattern"], If[branch["BaseMatchedQ"],matchedColor,unmatchedColor]]


BranchStyledPattern[branch_MatchBranchObject /; branch["Type"] === "Pattern"] :=
	Row[{
		Style[branch["Arguments"]["PatternVariable"], If[branch["BaseMatchedQ"],matchedColor,unmatchedColor]],
		Style[":", If[branch["BaseMatchedQ"],matchedColor,unmatchedColor]],
		BranchStyledPattern[branch["Arguments"]["Submatch"]]
	}]


BranchStyledPattern[branch_MatchBranchObject /; branch["Type"] === "PatternTest"] :=
	Row[{
		BranchStyledPattern[branch["Arguments"]["Submatch"]],
		Style["?", If[branch["BaseMatchedQ"],matchedColor,unmatchedColor]],
		Style[branch["Arguments"]["TestFunction"], If[branch["BaseMatchedQ"],matchedColor,unmatchedColor]]
	}]


BranchStyledPattern[branch_MatchBranchObject /; branch["Type"] === "Condition"] :=
	Row[{
		BranchStyledPattern[branch["Arguments"]["Submatch"]],
		Style[" /; ", If[branch["BaseMatchedQ"],matchedColor,unmatchedColor]],
		Style[HoldForm@@branch["Arguments"]["HeldCondition"], If[branch["BaseMatchedQ"],matchedColor,unmatchedColor]]
	}]


BranchStyledPattern[branch_MatchBranchObject /; branch["Type"] === "Alternatives"] :=
	Row[Riffle[
		ReplacePart[
			HoldForm@@@branch["Arguments"]["HeldBranchPatterns"],
			branch["Arguments"]["BranchIndex"] -> BranchStyledPattern[branch["Arguments"]["Submatch"]]
		],
		"|"
	]]


(* TODO: Doesn't display well if there are binding conflicts *)
BranchStyledPattern[branch_MatchBranchObject /; branch["Type"] === "Normal"] :=
	Row[{
		BranchStyledPattern[branch["Arguments"]["HeadSubmatch"]],
		Style["[", If[branch["BaseMatchedQ"],matchedColor,unmatchedColor]],
		Splice@Riffle[
			BranchStyledPattern/@branch["Arguments"]["ArgumentSubmatches"],
			Style[", ", If[branch["BaseMatchedQ"],matchedColor,unmatchedColor]]
		],
		Style["]", If[branch["BaseMatchedQ"],matchedColor,unmatchedColor]]
	}]


End[];
EndPackage[];
