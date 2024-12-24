Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem90463 : forall n : nat, forall m : nat, (Peano.gt m n) = (Peano.lt n m).
