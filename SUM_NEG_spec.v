Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7070827 : forall {_132004 : Type'}, forall f : _132004 -> real, forall s : _132004 -> Prop, (@sum _132004 s (fun x : _132004 => real_neg (f x))) = (real_neg (@sum _132004 s f)).
