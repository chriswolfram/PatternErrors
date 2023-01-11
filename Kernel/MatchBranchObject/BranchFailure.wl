BeginPackage["ChristopherWolfram`PatternErrors`MatchBranchObject`BranchFailure`"];

BranchFailure

Begin["`Private`"];

Needs["ChristopherWolfram`PatternErrors`"]


BranchFailure[branch_MatchBranchObject /; branch["MatchedQ"]] :=
	Success["Match", <|
		"Pattern" -> branch["Pattern"],
		"Expression" -> HoldForm@@branch["HeldExpression"],
		"MatchBranch" -> Iconize[branch]
	|>]


BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "Atomic"] :=
	Failure["AtomicMatchFailure", <|
		"MessageTemplate" -> "`1` does not match atomic pattern `2`.",
		"MessageParameters" -> {
			HoldForm@@branch["HeldExpression"],
			branch["Pattern"]
		},
		"Type" -> "Atomic",
		"MatchBranch" -> Iconize[branch]
	|>]


BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "Pattern"] :=
	If[branch["Arguments"]["BindingMatchedQ"],
	
		Failure["SubmatchFailure", <|
			"MessageTemplate" -> "`1` does not match `2` because it does not match `3`.",
			"MessageParameters" -> {
				HoldForm@@branch["HeldExpression"],
				branch["Pattern"],
				branch["Arguments"]["Submatch"]["Pattern"]
			},
			"Type" -> "Pattern",
			"Submatch" -> BranchFailure[branch["Arguments"]["Submatch"]],
			"MatchBranch" -> Iconize[branch]
		|>],
		
		Failure["BindingMatchFailure", <|
			"MessageTemplate" -> "`1` cannot be bound to `2` because it is already bound to `3`.",
			"MessageParameters" -> {
				HoldForm@@branch["HeldExpression"],
				branch["Pattern"],
				HoldForm@@Lookup[branch["Bindings"], branch["Arguments"]["PatternVariable"]]
			},
			"Type" -> "Pattern",
			"Submatch" -> BranchFailure[branch["Arguments"]["Submatch"]],
			"MatchBranch" -> Iconize[branch]
		|>]
		
	]


(* TODO: Improve failure when the expression is a sequence *)
BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "PatternTest"] :=
	If[branch["BaseMatchedQ"],
		
		Failure["SubmatchFailure", <|
			"MessageTemplate" -> "`1` does not match `2` because it does not match `3`.",
			"MessageParameters" -> {
				HoldForm@@branch["HeldExpression"],
				branch["Pattern"],
				branch["Arguments"]["Submatch"]["Pattern"]
			},
			"Type" -> "PatternTest",
			"Submatch" -> BranchFailure[branch["Arguments"]["Submatch"]],
			"MatchBranch" -> Iconize[branch]
		|>],
		
		Failure["PatternTestMatchFailure", <|
			"MessageTemplate" -> "`1` does not match `2` because it does not satisfy `3`.",
			"MessageParameters" -> {
				HoldForm@@branch["HeldExpression"],
				branch["Pattern"],
				branch["Arguments"]["TestFunction"]
			},
			"Type" -> "PatternTest",
			"Submatch" -> BranchFailure[branch["Arguments"]["Submatch"]],
			"MatchBranch" -> Iconize[branch]
		|>]

	]


BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "Alternatives"] :=
	Failure["BranchSubmatchFailure", <|
		"MessageTemplate" -> "`1` does not match the `2` branch of `3` because it does not match `4`.",
		"MessageParameters" -> {
			HoldForm@@branch["HeldExpression"],
			IntegerName[branch["Arguments"]["BranchIndex"], "Ordinal"],
			branch["Pattern"],
			branch["Arguments"]["Submatch"]["Pattern"]
		},
		"Type" -> "Alternatives",
		"Submatch" -> BranchFailure[branch["Arguments"]["Submatch"]],
		"MatchBranch" -> Iconize[branch]
	|>]


BranchFailure[branch_MatchBranchObject /; !branch["MatchedQ"] && branch["Type"] === "Normal"] :=
	Which[

		!branch["Arguments"]["HeadSubmatch"]["MatchedQ"],
			Failure["HeadMatchFailure", <|
				"MessageTemplate" -> "`1` does not match `2` because its head does not match `3`.",
				"MessageParameters" -> {
					HoldForm@@branch["HeldExpression"],
					branch["Pattern"],
					branch["HeadSubmatch"]["Pattern"]
				},
				"Type" -> "Normal",
				"HeadSubmatch" -> BranchFailure[branch["Arguments"]["HeadSubmatch"]],
				"ArgumentSubmatches" -> BranchFailure/@branch["Arguments"]["ArgumentSubmatches"],
				"MatchBranch" -> Iconize[branch]
			|>],

		Length[branch["Arguments"]["BindingConflicts"]] > 0,
			With[{bindingConflicts = branch["Arguments"]["BindingConflicts"]},
				Failure["IncompatibleBindingMatchFailure", <|
					(* TODO: Improve phrasing *)
					"MessageTemplate" -> "`1` does not match `2` because of in compatible bindings for the pattern variable `3` including `4`.",
					"MessageParameters" -> {
						HoldForm@@branch["HeldExpression"],
						branch["Pattern"],
						First[Keys[bindingConflicts]],
						First[Values[bindingConflicts]]
					},
					"Type" -> "Normal",
					"BindingConflicts" -> bindingConflicts
					"HeadSubmatch" -> BranchFailure[branch["Arguments"]["HeadSubmatch"]],
					"ArgumentSubmatches" -> BranchFailure/@branch["Arguments"]["ArgumentSubmatches"],
					"MatchBranch" -> Iconize[branch]
				|>]
			],
	
		True,
			With[{
				(*TODO: This is a bit unsafe*)
				argumentBranches = SelectFirst[branch["Arguments"]["ArgumentSubmatches"], !#["MatchedQ"]&]
			},
				Failure["ArgumentMatchFailure", <|
					(*TODO: Multiple arguments might fail, but this only mentions one. Maybe mention all of them?*)
					"MessageTemplate" -> "`1` does not match `2` because its argument `3` does not match `4`.",
					"MessageParameters" -> {
						HoldForm@@branch["HeldExpression"],
						branch["Pattern"],
						HoldForm@@argumentBranches["HeldExpression"],
						argumentBranches["Pattern"]
					},
					"Type" -> "Normal",
					"HeadSubmatch" -> BranchFailure[branch["Arguments"]["HeadSubmatch"]],
					"ArgumentSubmatches" -> BranchFailure/@branch["Arguments"]["ArgumentSubmatches"],
					"MatchBranch" -> Iconize[branch]
				|>]
			]
	
	]


End[];
EndPackage[];
