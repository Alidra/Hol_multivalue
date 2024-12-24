Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6958318 : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, ((@FINITE A s) /\ (exists x : A, (@IN A x s) /\ (Peano.lt (NUMERAL 0) (f x)))) -> Peano.lt (NUMERAL 0) (@nsum A s f).
