Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4010101 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall n : nat, ((@FINITE A s) /\ (Peano.le (@CARD A s) n)) -> (@FINITE B (@IMAGE A B f s)) /\ (Peano.le (@CARD B (@IMAGE A B f s)) n).
