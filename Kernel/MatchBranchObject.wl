BeginPackage["ChristopherWolfram`PatternErrors`MatchBranchObject`"];

Begin["`Private`"];

Needs["ChristopherWolfram`PatternErrors`"]


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
	Pattern: The pattern being matched.
	Bindings: Pattern variable bindings used at this part of the match
	MatchedQ: Whether this branch represents a successful match or not.
	BaseMatchedQ: False when this branch represents the root cause of a failed match.
*)

branchTypePattern = "Atomic" | "Pattern" | "PatternTest" | "Alternatives" | "Normal";

branchDataPattern = KeyValuePattern[{
	"Type" -> type:branchTypePattern,
	"Arguments" -> args_?AssociationQ,
	"HeldExpression" -> heldExpr_,
	"Pattern" -> patt_,
	"Bindings" -> bindings:{___Rule},
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
HoldPattern[MatchBranchObject][data:branchDataPattern][field_] :=
	data[field]

HoldPattern[MatchBranchObject][data:branchDataPattern][All] :=
	data


(* branchTypeArguments["Atomic"] :=
	KeyValuePattern[{}]?AssociationQ

branchTypeArguments["Pattern"] :=
	KeyValuePattern[{
		"Submatch" -> _MatchBranchObject,
		"BindingMatchedQ" -> _?BooleanQ
	}]?AssociationQ

branchTypeArguments["PatternTest"] :=
	KeyValuePattern[{
		"Submatch" -> _MatchBranchObject,
		"Tests" -> {___?BooleanQ}
	}]?AssociationQ

branchTypeArguments["Alternatives"] :=
	KeyValuePattern[{
		"Submatch" -> _MatchBranchObject,
		"Branch" -> _Integer
	}]?AssociationQ

branchTypeArguments["Normal"] :=
	KeyValuePattern[{
		"HeadSubmatch" -> _MatchBranchObject,
		"ArgumentSubmatches" -> {___MatchBranchObject}
	}]?AssociationQ *)


End[];
EndPackage[];
