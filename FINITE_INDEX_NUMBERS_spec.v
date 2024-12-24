Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5436088 : forall {A : Type'}, forall s : A -> Prop, (@FINITE A s) = (exists k : nat -> Prop, exists f : nat -> A, (forall i : nat, forall j : nat, ((@IN nat i k) /\ ((@IN nat j k) /\ ((f i) = (f j)))) -> i = j) /\ ((@FINITE nat k) /\ (s = (@IMAGE nat A f k)))).
