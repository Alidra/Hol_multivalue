Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2708269 : forall a : int, forall b : int, forall m : int, forall n : int, (@eq2 int a b (int_mod (int_mul m n))) -> @eq2 int (div a m) (div b m) (int_mod n).
