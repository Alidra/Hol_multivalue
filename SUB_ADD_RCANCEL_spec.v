Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem136770 : forall m : nat, forall n : nat, forall p : nat, (Nat.sub (Nat.add m p) (Nat.add n p)) = (Nat.sub m n).
