Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem100722 : forall m : nat, forall n : nat, (Peano.lt m (Nat.add m n)) = (Peano.lt (NUMERAL 0) n).
