Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem135886 : forall m : nat, forall n : nat, (Nat.sub (Nat.add m n) n) = m.
