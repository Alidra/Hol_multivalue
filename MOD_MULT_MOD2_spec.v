Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem205836 : forall m : nat, forall n : nat, forall p : nat, (Nat.modulo (Nat.mul (Nat.modulo m n) (Nat.modulo p n)) n) = (Nat.modulo (Nat.mul m p) n).
