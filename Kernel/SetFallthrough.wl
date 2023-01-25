BeginPackage["ChristopherWolfram`PatternErrors`SetFallthrough`"];

Begin["`Private`"];

Needs["ChristopherWolfram`PatternErrors`"]


(*
	SetFallthrough[f]
		creates a fallthrough definition of f so that f[___] will return a Failure.
*)

SetFallthrough[f_] :=
	(
		expr:HoldPattern[f][___] := ignoredValue@HeldMatchInformation[Hold[expr], downValuesPattern[f]]
	)

downValuesPattern[f_] :=
	With[{dv = DownValues[f]},
		If[!ListQ[dv],
			_,
			With[{patts = Keys@DeleteCases[dv, _[_, HoldPattern[ignoredValue][_]]]},
				Switch[Length[patts],
					0, _,
					1, First[patts],
					_, Alternatives@@patts
				]
			]
		]
	]


(* ignoredValue is a wrapper that can be put around the rhs of a down value to make it ignored by
this system. This exists to that SetFallthrough doesn't see its own fallthrough pattern. *)
ignoredValue[x_] := x



End[];
EndPackage[];
