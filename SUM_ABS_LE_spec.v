Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7083952 : forall {A : Type'}, forall f : A -> real, forall g : A -> real, forall s : A -> Prop, ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> real_le (real_abs (f x)) (g x))) -> real_le (real_abs (@sum A s f)) (@sum A s g).
