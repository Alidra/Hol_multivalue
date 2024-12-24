Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem100773 : forall m : nat, forall n : nat, (Peano.lt n (Nat.add m n)) = (Peano.lt (NUMERAL 0) m).
