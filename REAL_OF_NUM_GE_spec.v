Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483730 : forall m : nat, forall n : nat, (real_ge (real_of_num m) (real_of_num n)) = (Peano.ge m n).
