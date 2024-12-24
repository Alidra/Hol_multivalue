Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem135939 : forall m : nat, forall n : nat, (Nat.sub (Nat.add m n) m) = n.
