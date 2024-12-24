Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7083749 : forall {_132408 : Type'}, forall f : _132408 -> real, forall s : _132408 -> Prop, (@FINITE _132408 s) -> real_le (real_abs (@sum _132408 s f)) (@sum _132408 s (fun x : _132408 => real_abs (f x))).
