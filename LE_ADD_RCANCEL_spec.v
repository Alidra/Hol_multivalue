Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem100973 : forall m : nat, forall n : nat, forall p : nat, (Peano.le (Nat.add m p) (Nat.add n p)) = (Peano.le m n).
