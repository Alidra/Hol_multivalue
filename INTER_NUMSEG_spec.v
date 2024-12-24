Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5443756 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, (@INTER nat (dotdot m n) (dotdot p q)) = (dotdot (Nat.max m p) (Nat.min n q)).
