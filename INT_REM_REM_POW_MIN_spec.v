Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3070360 : forall x : int, forall p : int, forall m : nat, forall n : nat, (rem (rem x (int_pow p m)) (int_pow p n)) = (rem x (int_pow p (Nat.min m n))).
