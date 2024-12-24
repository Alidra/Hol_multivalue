Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483793 : forall m : nat, forall n : nat, (real_gt (real_of_num m) (real_of_num n)) = (Peano.gt m n).
