Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318990 : forall m : nat, forall n : nat, (hreal_mul (hreal_of_num m) (hreal_of_num n)) = (hreal_of_num (Nat.mul m n)).
