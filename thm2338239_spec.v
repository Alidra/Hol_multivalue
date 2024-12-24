Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2338239 : forall m : nat, forall n : nat, (Peano.lt n m) = (~ (Peano.le m n)).
