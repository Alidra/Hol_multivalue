Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem210821 : forall m : nat, forall n : nat, Peano.le (Nat.modulo m n) m.
