Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem274982 : forall P : nat -> Prop, forall n : nat, ((P n) /\ (forall m : nat, (Peano.lt m n) -> ~ (P m))) -> (minimal P) = n.
