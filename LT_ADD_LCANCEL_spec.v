Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem101108 : forall m : nat, forall n : nat, forall p : nat, (Peano.lt (Nat.add m n) (Nat.add m p)) = (Peano.lt n p).
