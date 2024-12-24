Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem101179 : forall m : nat, forall n : nat, forall p : nat, (Peano.lt (Nat.add m p) (Nat.add n p)) = (Peano.lt m n).
