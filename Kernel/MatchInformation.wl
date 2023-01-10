BeginPackage["ChristopherWolfram`PatternErrors`MatchInformation`"];

Begin["`Private`"];

Needs["ChristopherWolfram`PatternErrors`"]


(* Top-level functions *)

MatchInformation[expr_, patt_] :=
	MatchInformationObject[matchBranches[Hold[expr], patt, {}]]


(****************************************************************)
(************************* matchBranches ************************)
(****************************************************************)

(*
	matchBranches[heldExpr, patt, bindings]
		returns a list of MatchBranchObjects given a held expression, a pattern,
		and a set of bindings (from Pattern objects like x_).
*)


(* Atomic *)
(* TODO: should apply bindings before using MatchQ*)
matchBranches[heldExpr_, patt_, bindings_] :=
	If[MatchQ[heldExpr, Hold[patt]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]


(* Blank *)
(* TODO: Make these check the heads manually so that more specific MatchBranchObjects could be given. *)
matchBranches[heldExpr_, patt:Verbatim[Blank][], bindings_] :=
	If[MatchQ[heldExpr, Hold[_]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]

matchBranches[heldExpr_, patt:Verbatim[Blank][head_Symbol], bindings_] :=
	If[MatchQ[heldExpr, Hold[_head]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]


(* BlankSequence *)
(* TODO: Make these check the heads manually so that more specific MatchBranchObjects could be given. *)
matchBranches[heldExpr_, patt:Verbatim[BlankSequence][], bindings_] :=
	If[MatchQ[heldExpr, Hold[__]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]

matchBranches[heldExpr_, patt:Verbatim[BlankSequence][head_Symbol], bindings_] :=
	If[MatchQ[heldExpr, Hold[__head]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]


(* BlankNullSequence *)
matchBranches[heldExpr_, patt:Verbatim[BlankNullSequence][], bindings_] :=
	If[MatchQ[heldExpr, Hold[___]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]

matchBranches[heldExpr_, patt:Verbatim[BlankNullSequence][head_Symbol], bindings_] :=
	If[MatchQ[heldExpr, Hold[___head]],
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> True,
			"BaseMatchedQ" -> True
		|>]},
		{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}
	]


(* Pattern *)
matchBranches[heldExpr_, patt:Verbatim[Pattern][name_Symbol, subpatt_], bindings_] :=
	With[{
		bindingMatchedQ = !KeyExistsQ[bindings,name] || heldExpr === Lookup[bindings,name],
		submatches = matchBranches[heldExpr, subpatt, appendBindings[bindings,name->heldExpr]]
	},
		MatchBranchObject[<|
			"Type" -> "Pattern",
			"Arguments" -> <|
				"Submatch" -> #,
				"BindingMatchedQ" -> bindingMatchedQ
			|>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> #["Bindings"],
			"MatchedQ" -> #["MatchedQ"] && bindingMatchedQ,
			"BaseMatchedQ" -> bindingMatchedQ
		|>] &/@ submatches
	]

appendBindings[bindings_, new_] :=
	If[MemberQ[bindings, new], bindings, Append[bindings,new]]


(* PatternTest *)
matchBranches[heldExpr:Hold[exprs___], patt:Verbatim[PatternTest][subpatt_, test_], bindings_] :=
	With[{
		submatches = matchBranches[heldExpr, subpatt, bindings],
		testRes = test/@{exprs}
	},
	With[{
		testsPassedQ = AllTrue[testRes,TrueQ]
	},
		MatchBranchObject[<|
				"Type" -> "PatternTest",
				"Arguments" -> <|
					"Submatch" -> #,
					"Tests" -> testRes
				|>,
				"HeldExpression" -> heldExpr,
				"Pattern" -> patt,
				"Bindings" -> #["Bindings"],
				"MatchedQ" -> #["MatchedQ"] && testsPassedQ,
				"BaseMatchedQ" -> testsPassedQ
			|>] &/@ submatches
	]]


(* Alternatives *)
matchBranches[heldExpr_, patt:Verbatim[Alternatives][patts___], bindings_] :=
	Catenate@MapIndexed[
		MatchBranchObject[<|
			"Type" -> "Alternatives",
			"Arguments" -> <|
				"Submatch" -> #1,
				"Branch" -> First[#2]
			|>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> #1["Bindings"],
			"MatchedQ" -> #1["MatchedQ"],
			"BaseMatchedQ" -> True
		|>]&,
		matchBranches[heldExpr,#,bindings]&/@{patts},
		{2}
	]


(* Normal *)
(* TODO: What about attributes? *)
matchBranches[heldExpr:Hold[head_[args___]], patt:headPatt_[argPatts___], bindings_] :=
	With[{argGroups = argumentGroupings[Hold[args], {argPatts}]},
	With[{exprGroups = Prepend[Hold[head]]/@argGroups, patts = {headPatt, argPatts}},
	With[{matchChains = Catenate[matchFailureFold[#, patts, bindings] &/@ exprGroups]},
		If[Length[matchChains] === 0,
			{MatchBranchObject[<|
				"Type" -> "Atomic",
				"Arguments" -> <||>,
				"HeldExpression" -> heldExpr,
				"Pattern" -> patt,
				"Bindings" -> bindings,
				"MatchedQ" -> False,
				"BaseMatchedQ" -> False
			|>]},
			MatchBranchObject[<|
				"Type" -> "Normal",
				"Arguments" -> <|
					"HeadSubmatch" -> First[#],
					"ArgumentSubmatches" -> Rest[#]
				|>,
				"HeldExpression" -> heldExpr,
				"Pattern" -> patt,
				"Bindings" -> Last[#]["Bindings"],
				"MatchedQ" -> AllTrue[#,#["MatchedQ"]&],
				"BaseMatchedQ" -> True
			|>] &/@ matchChains
		]
	]]]


matchBranches[heldExpr:Hold[expr_], patt:headPatt_[argPatts___], bindings_] :=
	{MatchBranchObject[<|
			"Type" -> "Atomic",
			"Arguments" -> <||>,
			"HeldExpression" -> heldExpr,
			"Pattern" -> patt,
			"Bindings" -> bindings,
			"MatchedQ" -> False,
			"BaseMatchedQ" -> False
		|>]}


(*
	argumentGroupings[heldExpr, argPattsList]
		returns a all possible groupings of arguments that are plausible given the given
		argument patterns.
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
	matchFailureFold[heldExprs, patt, bindings]
		takes parallel lists of held expressions and associated patterns and
		returns a (parallel) list of MatchInfo objects representing matches of
		each held expression with its associated pattern.
		
		This function is nontrivial because bindings from the first match have
		to be taken into account when performing the next match.
*)

matchFailureFold[heldExprs_, patts_, bindings_] :=
	Fold[
		{allPreviousMatches, newInputs} |->
			Catenate@Map[
				previousMatch |->
					Append[previousMatch,#]&/@
						matchBranches[newInputs[[1]], newInputs[[2]], Last[previousMatch]["Bindings"]],
				allPreviousMatches
			],
		List/@matchBranches[First[heldExprs], First[patts], bindings],
		Rest@MapThread[List, {heldExprs, patts}]
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
