Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem182819 : forall m : nat, forall n : nat, forall p : nat, (Nat.modulo (Nat.modulo m (Nat.mul n p)) n) = (Nat.modulo m n).
