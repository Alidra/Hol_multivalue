Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3070924 : forall a : nat, forall b : nat, forall m : nat, forall n : nat, (@eq2 nat a b (num_mod (Nat.mul m n))) -> @eq2 nat (Nat.div a m) (Nat.div b m) (num_mod n).
