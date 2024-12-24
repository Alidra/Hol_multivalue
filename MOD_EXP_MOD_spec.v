Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem206228 : forall m : nat, forall n : nat, forall p : nat, (Nat.modulo (Nat.pow (Nat.modulo m n) p) n) = (Nat.modulo (Nat.pow m p) n).
