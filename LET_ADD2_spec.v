Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem101695 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, ((Peano.le m p) /\ (Peano.lt n q)) -> Peano.lt (Nat.add m n) (Nat.add p q).
