Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem282171 : forall P : nat -> Prop, forall n : nat, ((exists r : nat, P r) /\ (forall m : nat, (Peano.lt m n) -> ~ (P m))) -> Peano.le n (minimal P).
