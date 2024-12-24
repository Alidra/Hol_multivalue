Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1640492 : forall x : real, forall m : nat, forall n : nat, (real_pow (real_pow x m) n) = (real_pow x (Nat.mul m n)).
