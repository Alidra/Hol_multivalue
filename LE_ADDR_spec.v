Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem100562 : forall m : nat, forall n : nat, Peano.le n (Nat.add m n).
