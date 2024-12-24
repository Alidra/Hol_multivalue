Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem91305 : forall m : nat, forall n : nat, (Peano.lt m (S n)) = (Peano.le m n).
