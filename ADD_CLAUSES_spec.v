Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem77629 : (forall n : nat, (Nat.add (NUMERAL 0) n) = n) /\ ((forall m : nat, (Nat.add m (NUMERAL 0)) = m) /\ ((forall m : nat, forall n : nat, (Nat.add (S m) n) = (S (Nat.add m n))) /\ (forall m : nat, forall n : nat, (Nat.add m (S n)) = (S (Nat.add m n))))).
