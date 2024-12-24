Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1269222 : forall m : nat, forall n : nat, (nadd_eq (nadd_of_num m) (nadd_of_num n)) = (m = n).
