Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem77960 : forall m : nat, forall n : nat, forall p : nat, (Nat.add m (Nat.add n p)) = (Nat.add (Nat.add m n) p).
