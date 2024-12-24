Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem227406 : forall m : nat, forall n : nat, forall p : nat, (Nat.modulo (Nat.div m n) p) = (Nat.div (Nat.modulo m (Nat.mul n p)) n).
