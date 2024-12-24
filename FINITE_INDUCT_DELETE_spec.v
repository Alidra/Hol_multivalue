Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3862701 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, ((P (@EMPTY A)) /\ (forall s : A -> Prop, ((@FINITE A s) /\ (~ (s = (@EMPTY A)))) -> exists x : A, (@IN A x s) /\ ((P (@DELETE A s x)) -> P s))) -> forall s : A -> Prop, (@FINITE A s) -> P s.
