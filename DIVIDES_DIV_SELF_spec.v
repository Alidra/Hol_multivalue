Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3112963 : forall n : nat, forall d : nat, (num_divides d n) -> num_divides (Nat.div n d) n.
