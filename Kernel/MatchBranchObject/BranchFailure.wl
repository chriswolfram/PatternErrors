BeginPackage["ChristopherWolfram`PatternErrors`MatchBranchObject`BranchFailure`"];

BranchFailure

Begin["`Private`"];

Needs["ChristopherWolfram`PatternErrors`"]


BranchFailure[branch_MatchBranchObject /; branch["MatchedQ"]] :=
	Success["Match", <|
		"Pattern" -> branch["Pattern"],
		"Expression" -> HoldForm@@branch["HeldExpression"],
		"Bindings" -> branch["Bindings"],
		"MatchBranch" -> Iconize[branch]
	|>]


BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "Atomic"] :=
	Failure["AtomicMatchFailure", <|
		"MessageTemplate" -> "Expected expression matching `2`, but found `1` instead.",
		"MessageParameters" -> {
			HoldForm@@branch["HeldExpression"],
			branch["Pattern"]
		},
		"Type" -> "Atomic",
		"Bindings" -> branch["Bindings"],
		"MatchBranch" -> Iconize[branch]
	|>]


BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "Pattern"] :=
	If[branch["Arguments"]["BindingMatchedQ"],
	
		BranchFailure[branch["Arguments"]["Submatch"]],
		
		Failure["BindingMatchFailure", <|
			"MessageTemplate" -> "`1` cannot be bound to `2` because it is already bound to `3`.",
			"MessageParameters" -> {
				HoldForm@@branch["HeldExpression"],
				branch["Pattern"],
				HoldForm@@Lookup[branch["Bindings"], branch["Arguments"]["PatternVariable"]]
			},
			"Type" -> "Pattern",
			"Submatch" -> BranchFailure[branch["Arguments"]["Submatch"]],
			"Bindings" -> branch["Bindings"],
			"MatchBranch" -> Iconize[branch]
		|>]
		
	]


(* TODO: Improve failure when the expression is a sequence *)
BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "PatternTest"] :=
	If[branch["BaseMatchedQ"],
		
		BranchFailure[branch["Arguments"]["Submatch"]],
		
		Failure["PatternTestMatchFailure", <|
			"MessageTemplate" -> "Expected an expression satisfying `2`, but found `1` instead.",
			"MessageParameters" -> {
				HoldForm@@branch["HeldExpression"],
				branch["Arguments"]["TestFunction"]
			},
			"Type" -> "PatternTest",
			"TestResults" -> branch["Arguments"]["TestResults"],
			"Submatch" -> BranchFailure[branch["Arguments"]["Submatch"]],
			"Bindings" -> branch["Bindings"],
			"MatchBranch" -> Iconize[branch]
		|>]

	]


(* TODO: Improve failure when the expression is a sequence *)
BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "Condition"] :=
	If[branch["BaseMatchedQ"],
		
		BranchFailure[branch["Arguments"]["Submatch"]],
		
		Failure["ConditionMatchFailure", <|
			"MessageTemplate" -> "Condition `1` not satisfied, returning `2`.",
			"MessageParameters" -> {
				HoldForm@@branch["Arguments"]["HeldCondition"],
				branch["Arguments"]["ConditionResult"]
			},
			"Type" -> "Condition",
			"ConditionResult" -> branch["Arguments"]["ConditionResult"],
			"Submatch" -> BranchFailure[branch["Arguments"]["Submatch"]],
			"Bindings" -> branch["Bindings"],
			"MatchBranch" -> Iconize[branch]
		|>]

	]


BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "Alternatives"] :=
	BranchFailure[branch["Arguments"]["Submatch"]]


BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "Normal"] :=
	With[{
		failedArgumentIndex = First@FirstPosition[
			branch["Arguments"]["ArgumentSubmatches"],
			_?(!#["MatchedQ"]&),
			{Missing[]}, {1}, Heads->False
		]
	},
		Which[

			!branch["Arguments"]["HeadSubmatch"]["MatchedQ"],
				Failure["HeadMatchFailure", <|
					"MessageTemplate" -> "Expected head matching `1`, but found `2` instead.",
					"MessageParameters" -> {
						branch["HeadSubmatch"]["Pattern"],
						HoldForm@@branch["HeadSubmatch"]["HeldExpression"]
					},
					"Type" -> "Normal",
					"HeadSubmatch" -> BranchFailure[branch["Arguments"]["HeadSubmatch"]],
					"ArgumentSubmatches" -> BranchFailure/@branch["Arguments"]["ArgumentSubmatches"],
					"Bindings" -> branch["Bindings"],
					"MatchBranch" -> Iconize[branch]
				|>],

			Length[branch["Arguments"]["BindingConflicts"]] > 0,
				With[{bindingConflicts = branch["Arguments"]["BindingConflicts"]},
					Failure["IncompatibleBindingMatchFailure", <|
						"MessageTemplate" -> "Encountered incompatible bindings for the pattern variable `1`, including: `2`",
						"MessageParameters" -> {
							First[Keys[bindingConflicts]],
							First[Values[bindingConflicts]]
						},
						"Type" -> "Normal",
						"BindingConflicts" -> bindingConflicts,
						"HeadSubmatch" -> BranchFailure[branch["Arguments"]["HeadSubmatch"]],
						"ArgumentSubmatches" -> BranchFailure/@branch["Arguments"]["ArgumentSubmatches"],
						"Bindings" -> branch["Bindings"],
						"MatchBranch" -> Iconize[branch]
					|>]
				],
		
			IntegerQ[failedArgumentIndex],
				Failure["ArgumentMatchFailure", <|
					(*TODO: Multiple arguments might fail, but this only mentions one. Maybe mention all of them?*)
					"MessageTemplate" -> "Expected an expression matching `1` in the `2` argument of `3`, but found `4` instead.",
					"MessageParameters" -> {
						branch["Arguments"]["ArgumentSubmatches"][[failedArgumentIndex]]["Pattern"],
						IntegerName[failedArgumentIndex, "Ordinal"],
						branch["Pattern"],
						HoldForm@@branch["Arguments"]["ArgumentSubmatches"][[failedArgumentIndex]]["HeldExpression"]
					},
					"Type" -> "Normal",
					"HeadSubmatch" -> BranchFailure[branch["Arguments"]["HeadSubmatch"]],
					"ArgumentSubmatches" -> BranchFailure/@branch["Arguments"]["ArgumentSubmatches"],
					"Bindings" -> branch["Bindings"],
					"MatchBranch" -> Iconize[branch]
				|>],

			(* TODO: Add better fallthrough case (on all of these) *)
			True,
				$Failed
		
		]
	]


End[];
EndPackage[];
