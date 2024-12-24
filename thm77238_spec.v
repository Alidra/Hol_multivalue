Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem77238 : (forall n : nat, (Nat.add (NUMERAL 0) n) = n) /\ (forall m : nat, forall n : nat, (Nat.add (S m) n) = (S (Nat.add m n))).
