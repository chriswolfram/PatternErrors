BeginPackage["ChristopherWolfram`PatternErrors`MatchBranchObject`"];

Begin["`Private`"];

Needs["ChristopherWolfram`PatternErrors`"]
Needs["ChristopherWolfram`PatternErrors`MatchBranchObject`BranchFailure`"]
Needs["ChristopherWolfram`PatternErrors`MatchBranchObject`BranchStyledPattern`"]


(*
	MatchBranchObject represents a leaf in the match tree. That is, it represents a single
	path down the tree of possible matching decisions, containing information about what
	matched and what didn't.

	MatchBranchObjects contain basic information about the target pattern and expression, as
	well as arguments that are specific to the kind of pattern (e.g. Alternatives, Blank, etc.)

	The target expression is always passed around in a Hold, and it can be a sequence.

	Type: The type of pattern that the top-level of this branch represents.
	Arguments: Type-specific arguments.
	HeldExpression: A held (with Hold) version of the matched expression.
	HeldPattern: A held (with Hold) version of the pattern being matched.
	Bindings: Pattern variable bindings used at this part of the match
	MatchedQ: Whether this branch represents a successful match or not.
	BaseMatchedQ: False when this branch represents the root cause of a failed match.
*)


(*
	Type specific arguments:

	"Atomic"
	<||>

	"Pattern"
	<|
		"Submatch" -> _MatchBranchObject,
		"BindingMatchedQ" -> _?BooleanQ,
		"PatternVariable" -> _Symbol
	|>

	"PatternTest"
	<|
		"Submatch" -> _MatchBranchObject,
		"TestResults" -> {___},
		"TestFunction" -> _
	|>

	"Condition"
	<|
		"Submatch" -> _MatchBranchObject,
		"ConditionResult" -> _,
		"HeldCondition" -> _
	|>

	"Alternatives"
	<|
		"Submatch" -> _MatchBranchObject,
		"HeldBranchPatterns" -> {___},
		"BranchIndex" -> _Integer
	|>

	"Normal"
	<|
		"HeadSubmatch" -> _MatchBranchObject,
		"ArgumentSubmatches" -> {___MatchBranchObject},
		"BindingConflicts" -> <|_Symbol -> {Repeated[_Hold, {2,Infinity}]}|>
	|>
*)

branchTypePattern = "Atomic" | "Pattern" | "PatternTest" | "Condition" | "Alternatives" | "Normal";

branchDataPattern = KeyValuePattern[{
	"Type" -> type:branchTypePattern,
	"Arguments" -> args_?AssociationQ,
	"HeldExpression" -> heldExpr_Hold,
	"HeldPattern" -> heldPatt_Hold,
	"Bindings" -> bindings_?AssociationQ,
	"MatchedQ" -> matchedQ_?BooleanQ,
	"BaseMatchedQ" -> baseMatchedQ_?BooleanQ
}]?AssociationQ;


(* Verifier *)

HoldPattern[MatchBranchObject][data:Except[branchDataPattern]] :=
	Failure["InvalidMatchBranchObject", <|
		"MessageTemplate" :> MatchBranchObject::invMatchBranchObject,
		"MessageParameters" -> {data},
		"Data" -> data 
	|>]


(* Accessors *)

HoldPattern[MatchBranchObject][data:branchDataPattern][All] :=
	data

branch_MatchBranchObject[field_] :=
	branch[All][field]

branch_MatchBranchObject["Failure"] :=
	BranchFailure[branch]

branch_MatchBranchObject["StyledPattern"] :=
	BranchStyledPattern[branch]

(* TODO: This is a slightly unsafe way to do this: *)
branch_MatchBranchObject["MatchRatio"] :=
	Count[branch, b_MatchBranchObject /; b["BaseMatchedQ"], {0,Infinity}] /
	Count[branch, b_MatchBranchObject, {0,Infinity}]


(* Formatting *)

MatchBranchObject /: Format[branch_MatchBranchObject /; branch["Type"] === "Atomic"] :=
	Interpretation[
		Panel@branchOpenerHeader[branch],
		branch
	]


MatchBranchObject /: Format[branch_MatchBranchObject /; branch["Type"] === "Pattern"] :=
	Interpretation[
		Panel@OpenerView[{
			branchOpenerHeader[branch],
			Row[{"Submatch: ", branch["Arguments"]["Submatch"]}]
		}],
		branch
	]


MatchBranchObject /: Format[branch_MatchBranchObject /; branch["Type"] === "PatternTest"] :=
	Interpretation[
		Panel[OpenerView[{
			branchOpenerHeader[branch],
			Column[{
				Row[{"Test results: ", branch["Arguments"]["TestResults"]}],
				Row[{"Submatch: ", branch["Arguments"]["Submatch"]}]
			}]
		}]],
		branch
	]


MatchBranchObject /: Format[branch_MatchBranchObject /; branch["Type"] === "Condition"] :=
	Interpretation[
		Panel[OpenerView[{
			branchOpenerHeader[branch],
			Column[{
				Row[{"Condition result: ", branch["Arguments"]["ConditionResult"]}],
				Row[{"Bindings: ", branch["Bindings"]}],
				Row[{"Submatch: ", branch["Arguments"]["Submatch"]}]
			}]
		}]],
		branch
	]


MatchBranchObject /: Format[branch_MatchBranchObject /; branch["Type"] === "Alternatives"] :=
	Interpretation[
		Panel[OpenerView[{
			branchOpenerHeader[branch],
			Column[{
				Row[{"Branch index: ", branch["Arguments"]["BranchIndex"]}],
				Row[{"Submatch: ", branch["Arguments"]["Submatch"]}]
			}]
		}]],
		branch
	]


MatchBranchObject /: Format[branch_MatchBranchObject /; branch["Type"] === "Normal"] :=
	Interpretation[
		Panel[OpenerView[{
			branchOpenerHeader[branch],
			Column[{
				Row[{"Binding conflicts: ", branch["Arguments"]["BindingConflicts"]}],
				Row[{"Head submatch: ", branch["Arguments"]["HeadSubmatch"]}],
				OpenerView[{
					"Argument submatches",
					Column[branch["Arguments"]["ArgumentSubmatches"]]
				}]
			}]
		}]],
		branch
	]


branchOpenerHeader[branch_] :=
	With[{fail = branch["Failure"]},
		If[FailureQ[fail],
			Column[{
				branch["Failure"]["Message"],
				branch["StyledPattern"]
			}],
			branch["StyledPattern"]
		]
	]



End[];
EndPackage[];
