Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7197663 : forall {A B : Type'}, forall f : A -> B, forall g : B -> real, forall s : A -> Prop, ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> real_le (real_of_num (NUMERAL 0)) (g (f x)))) -> real_le (@sum B (@IMAGE A B f s) g) (@sum A s (@o A B real g f)).
