Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5423178 : forall {A : Type'}, forall s : A -> Prop, (@FINITE A s) = (exists f : nat -> A, (forall i : nat, forall j : nat, ((@IN nat i (dotdot (NUMERAL (BIT1 0)) (@CARD A s))) /\ ((@IN nat j (dotdot (NUMERAL (BIT1 0)) (@CARD A s))) /\ ((f i) = (f j)))) -> i = j) /\ (s = (@IMAGE nat A f (dotdot (NUMERAL (BIT1 0)) (@CARD A s))))).
