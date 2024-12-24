Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem136356 : forall m : nat, forall n : nat, (Nat.sub n (Nat.add m n)) = (NUMERAL 0).
