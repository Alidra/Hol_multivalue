Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308910 : forall x : int, forall m : nat, forall n : nat, (int_pow (int_pow x m) n) = (int_pow x (Nat.mul m n)).
