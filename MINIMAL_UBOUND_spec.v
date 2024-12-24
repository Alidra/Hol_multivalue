Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem280136 : forall P : nat -> Prop, forall n : nat, (P n) -> Peano.le (minimal P) n.
