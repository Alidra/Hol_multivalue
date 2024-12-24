Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1273144 : forall x : nadd, exists n : nat, nadd_le x (nadd_of_num n).
