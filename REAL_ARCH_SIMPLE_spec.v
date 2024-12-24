Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1698434 : forall x : real, exists n : nat, real_le x (real_of_num n).
