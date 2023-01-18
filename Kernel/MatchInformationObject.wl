BeginPackage["ChristopherWolfram`PatternErrors`MatchInformationObject`"];

Begin["`Private`"];

Needs["ChristopherWolfram`PatternErrors`"]


(*
	MatchInformationObject represents a the entire match tree. It is essentially a list of
	MatchBranchObjects.
*)

(* Verifier *)

HoldPattern[MatchInformationObject][branches:Except[{___MatchBranchObject}]] :=
	Failure["InvalidMatchInformationObject", <|
		"MessageTemplate" :> MatchInformationObject::invMatchInformationObject,
		"MessageParameters" -> {branches},
		"Branches" -> branches 
	|>]


(* Accessors *)

HoldPattern[MatchInformationObject][branches:{___MatchBranchObject}]["Branches"] :=
	branches


(* Formatting *)

MatchInformationObject /: Format[matchInfo_MatchInformationObject] :=
	Interpretation[
		Row[{
			"MatchInformationObject[",
			MenuView[#["StyledPattern"] -> # &/@ ReverseSortBy[matchInfo["Branches"], #["MatchRatio"]&]],
			"]"
		}],
		matchInfo
	]



End[];
EndPackage[];
