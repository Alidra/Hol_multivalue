Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem79714 : forall m : nat, forall n : nat, forall p : nat, ((Nat.add m p) = (Nat.add n p)) = (m = n).
