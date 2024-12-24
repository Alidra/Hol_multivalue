Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1484027 : forall m : nat, forall n : nat, (real_min (real_of_num m) (real_of_num n)) = (real_of_num (Nat.min m n)).
