Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318825 : forall m : nat, forall n : nat, ((hreal_of_num m) = (hreal_of_num n)) = (m = n).
