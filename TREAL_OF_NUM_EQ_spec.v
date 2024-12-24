Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1326943 : forall m : nat, forall n : nat, (treal_eq (treal_of_num m) (treal_of_num n)) = (m = n).
