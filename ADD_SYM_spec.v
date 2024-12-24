Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem77775 : forall m : nat, forall n : nat, (Nat.add m n) = (Nat.add n m).
