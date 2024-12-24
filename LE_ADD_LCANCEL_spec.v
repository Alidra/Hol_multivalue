Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem100902 : forall m : nat, forall n : nat, forall p : nat, (Peano.le (Nat.add m n) (Nat.add m p)) = (Peano.le n p).
