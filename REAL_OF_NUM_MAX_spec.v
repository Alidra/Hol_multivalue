Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483910 : forall m : nat, forall n : nat, (real_max (real_of_num m) (real_of_num n)) = (real_of_num (Nat.max m n)).
