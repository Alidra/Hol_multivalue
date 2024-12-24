Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1269004 : forall m : nat, forall n : nat, (m = n) -> nadd_eq (nadd_of_num m) (nadd_of_num n).
