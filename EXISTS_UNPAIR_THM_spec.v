Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem54104 : forall {_5515 _5517 : Type'}, forall P : _5515 -> _5517 -> Prop, (exists x : _5515, exists y : _5517, P x y) = (exists z : prod _5515 _5517, P (@fst _5515 _5517 z) (@snd _5515 _5517 z)).
