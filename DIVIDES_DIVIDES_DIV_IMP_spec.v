Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3114294 : forall n : nat, forall d : nat, forall e : nat, (num_divides (Nat.mul d e) n) -> num_divides e (Nat.div n d).
