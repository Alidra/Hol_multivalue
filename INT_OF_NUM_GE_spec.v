Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307172 : forall m : nat, forall n : nat, (int_ge (int_of_num m) (int_of_num n)) = (Peano.ge m n).
