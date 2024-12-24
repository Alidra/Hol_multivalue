Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1332671 : forall m : nat, forall n : nat, (m = n) -> treal_eq (treal_of_num m) (treal_of_num n).
