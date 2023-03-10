BeginPackage["ChristopherWolfram`PatternErrors`MatchInformation`"];

Begin["`Private`"];

Needs["ChristopherWolfram`PatternErrors`"]


(* Top-level functions *)

MatchInformation[expr_, patt_] :=
	MatchInformationObject[HeldMatchInformation[Hold[expr], patt]]


(****************************************************************)
(************************* HeldMatchInformation ************************)
(****************************************************************)

(*
	HeldMatchInformation[heldExpr, patt]
		returns a list of MatchBranchObjects given a held expression and a pattern.
*)


(* Atomic *)
(* TODO: This should eventually be removed because it ignores bindings (among other things) *)
HeldMatchInformation[heldExpr_, patt_] :=
	If[MatchQ[heldExpr, Hold[patt]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]


(* Blank *)
(* TODO: Make these check the heads manually so that more specific MatchBranchObjects could be given. *)
HeldMatchInformation[heldExpr_, patt:Verbatim[Blank][]] :=
	If[MatchQ[heldExpr, Hold[_]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]

HeldMatchInformation[heldExpr_, patt:Verbatim[Blank][head_Symbol]] :=
	If[MatchQ[heldExpr, Hold[_head]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]


(* BlankSequence *)
(* TODO: Make these check the heads manually so that more specific MatchBranchObjects could be given. *)
HeldMatchInformation[heldExpr_, patt:Verbatim[BlankSequence][]] :=
	If[MatchQ[heldExpr, Hold[__]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]

HeldMatchInformation[heldExpr_, patt:Verbatim[BlankSequence][head_Symbol]] :=
	If[MatchQ[heldExpr, Hold[__head]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]


(* BlankNullSequence *)
HeldMatchInformation[heldExpr_, patt:Verbatim[BlankNullSequence][]] :=
	If[MatchQ[heldExpr, Hold[___]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]

HeldMatchInformation[heldExpr_, patt:Verbatim[BlankNullSequence][head_Symbol]] :=
	If[MatchQ[heldExpr, Hold[___head]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> <||>,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]


(* Pattern *)
HeldMatchInformation[heldExpr_, patt:Verbatim[Pattern][name_Symbol, subpatt_]] :=
	With[{submatches = HeldMatchInformation[heldExpr, subpatt]},
		With[{bindingMatchedQ = !KeyExistsQ[#["Bindings"],name] || heldExpr === Lookup[#["Bindings"],name]},
			MatchBranchObject[<|
				"Type" -> "Pattern",
				"Arguments" -> <|
					"Submatch" -> #,
					"BindingMatchedQ" -> bindingMatchedQ,
					"PatternVariable" -> name
				|>,
				"HeldExpression" -> heldExpr,
				"Pattern" -> patt,
				"Bindings" -> Append[#["Bindings"], name->heldExpr],
				"MatchedQ" -> #["MatchedQ"] && bindingMatchedQ,
				"BaseMatchedQ" -> bindingMatchedQ
			|>]
		] &/@ submatches
	]


(* PatternTest *)
(* TODO: test should probably be contained in Hold because PatternTest is HoldRest *)
HeldMatchInformation[heldExpr:Hold[exprs___], patt:Verbatim[PatternTest][subpatt_, test_]] :=
	With[{
		submatches = HeldMatchInformation[heldExpr, subpatt],
		testRes = test/@{exprs}
	},
	With[{
		testsPassedQ = AllTrue[testRes,TrueQ]
	},
		MatchBranchObject[<|
			"Type" -> "PatternTest",
			"Arguments" -> <|
				"Submatch" -> #,
				"TestResults" -> testRes,
				"TestFunction" -> test
			|>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> #["Bindings"],
			"MatchedQ" -> #["MatchedQ"] && testsPassedQ,
			"BaseMatchedQ" -> testsPassedQ
		|>] &/@ submatches
	]]


(* Condition *)
HeldMatchInformation[heldExpr:Hold[exprs___], patt:Verbatim[Condition][subpatt_, cond_]] :=
	With[{submatches = HeldMatchInformation[heldExpr, subpatt]},
	With[{submatchTestRes = evaluateCondition[Hold[cond], #["Bindings"]] &/@ submatches},
		MapThread[
			MatchBranchObject[<|
				"Type" -> "Condition",
				"Arguments" -> <|
					"Submatch" -> #1,
					"ConditionResult" -> #2,
					"HeldCondition" -> Hold[cond]
				|>,
				"HeldExpression" -> heldExpr,
				"Pattern" -> patt,
				"Bindings" -> #1["Bindings"],
				"MatchedQ" -> #1["MatchedQ"] && TrueQ[#2],
				"BaseMatchedQ" -> TrueQ[#2]
			|>]&,
			{submatches, submatchTestRes}
		]
	]]


evaluateCondition[heldCond_, bindings_] :=
	First@ReplaceAll[
		heldCond,
		Replace[
			RuleDelayed@@@Normal[bindings],
			(sym_ :> Hold[val___]) :> (sym :> Sequence[val]),
			{1}
		]
	]


(* Alternatives *)
HeldMatchInformation[heldExpr_, patt:Verbatim[Alternatives][patts___]] :=
	Catenate@MapIndexed[
		MatchBranchObject[<|
			"Type" -> "Alternatives",
			"Arguments" -> <|
				"Submatch" -> #1,
				"BranchIndex" -> First[#2]
			|>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> #1["Bindings"],
			"MatchedQ" -> #1["MatchedQ"],
			"BaseMatchedQ" -> True
		|>]&,
		HeldMatchInformation[heldExpr,#]&/@{patts},
		{2}
	]


(* Normal *)
(* TODO: What about attributes? *)
HeldMatchInformation[heldExpr:Hold[head_[args___]], patt:headPatt_[argPatts___]] :=
	With[{argGroups = argumentGroupings[Hold[args], {argPatts}]},
	With[{exprGroups = Prepend[Hold[head]]/@argGroups},
	With[{patts = {headPatt, argPatts}},
	With[{headArgumentMatches = Catenate[Tuples[MapThread[HeldMatchInformation, {#, patts}]]&/@exprGroups]},
		(matchList |->
			With[{bindingLists = Merge[#["Bindings"]&/@matchList, DeleteDuplicates]},
			With[{bindingConflicts = Select[bindingLists, Length[#]>1&]},
				MatchBranchObject[<|
					"Type" -> "Normal",
					"Arguments" -> <|
						"HeadSubmatch" -> First[matchList],
						"ArgumentSubmatches" -> Rest[matchList],
						"BindingConflicts" -> bindingConflicts
					|>,
					"HeldExpression" -> heldExpr,
					"Pattern" -> patt,
					"Bindings" -> bindingLists[[All,1]],
					"MatchedQ" -> AllTrue[matchList,#["MatchedQ"]&] && Length[bindingConflicts] === 0,
					"BaseMatchedQ" -> Length[bindingConflicts] === 0
				|>]
			]]
		) /@ headArgumentMatches
	]]]]


HeldMatchInformation[heldExpr:Hold[expr_], patt:headPatt_[argPatts___]] :=
	{MatchBranchObject[<|
		"Type" -> "Atomic",
		"Arguments" -> <||>,
		"HeldExpression" -> heldExpr,
		"Pattern" -> patt,
		"Bindings" -> {},
		"MatchedQ" -> False,
		"BaseMatchedQ" -> False
	|>]}


(*
	argumentGroupings[heldExpr, argPattsList]
		returns a all possible groupings of arguments that are plausible given the given
		argument patterns.

	Returns in the form {{Hold[a],Hold[b,c]}, {Hold[a,b],Hold[c]}, ...}
*)
argumentGroupings[heldExpr_, argPattsList_] :=
	With[{
		blankPatterns = blankPattern/@argPattsList,
		patternSymbols = Table[Unique[], Length[argPattsList]]
	},
		ReplaceList[
			heldExpr,
			Hold@@MapThread[Pattern,{patternSymbols,blankPatterns}] -> Hold/@patternSymbols
		]
	]


(*
	blankPattern[patt]
		returns a schematic version of patt that matches a sequence of the same length as patt.
*)
blankPattern[patt_] := _

blankPattern[Verbatim[Blank][]] := _
blankPattern[Verbatim[Blank][head_]] := _
blankPattern[Verbatim[BlankSequence][]] := __
blankPattern[Verbatim[BlankSequence][head_]] := __
blankPattern[Verbatim[BlankNullSequence][]] := ___
blankPattern[Verbatim[BlankNullSequence][head_]] := ___

blankPattern[Verbatim[Pattern][sym_, patt_]] := blankPattern[patt]

blankPattern[Verbatim[PatternTest][patt_, test_]] := blankPattern[patt]

blankPattern[Verbatim[Repeated][patt_]] := Repeated[blankPattern[patt]]
blankPattern[Verbatim[Repeated][patt_, spec_]] := Repeated[blankPattern[patt], spec]
blankPattern[Verbatim[RepeatedNull][patt_]] := RepeatedNull[blankPattern[patt]]
blankPattern[Verbatim[RepeatedNull][patt_, spec_]] := RepeatedNull[blankPattern[patt], spec]

blankPattern[Verbatim[Optional][patt_, def_]] := RepeatedNull[blankPattern[patt], {0,1}]

blankPattern[Verbatim[Alternatives][branches___]] := Alternatives@@(blankPattern/@{branches})

blankPattern[Verbatim[Condition][patt_, test_]] := blankPattern[patt]

(*blankPattern[Verbatim[HoldPattern][patt_]] := blankPattern[patt]
blankPattern[Verbatim[Literal][patt_]] := blankPattern[patt]*)

blankPattern[Verbatim[Verbatim][expr_]] := _

(*TODO: confirm this*)
blankPattern[Verbatim[Except][patt_]] := _

blankPattern[Verbatim[Shortest][patt_]] := Shortest[blankPattern[patt]]
blankPattern[Verbatim[Longest][patt_]] := Longest[blankPattern[patt]]

blankPattern[Verbatim[OptionsPattern][___]] := ___

blankPattern[Verbatim[PatternSequence][patts___]] := PatternSequence@@(blankPattern/@{patts})
blankPattern[Verbatim[OrderlessPatternSequence][patts___]] := OrderlessPatternSequence@@(blankPattern/@{patts})

blankPattern[Verbatim[KeyValuePattern][patt_]] := _

(*
Missing:
IgnoreInactive
InertSequence
AssociationPattern
*)


End[];
EndPackage[];
