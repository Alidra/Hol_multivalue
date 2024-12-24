Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem272789 : forall m : nat, forall n : nat, (m = (Nat.add m n)) = (n = (NUMERAL 0)).
