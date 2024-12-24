Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem290135 : forall R : nat -> nat -> Prop, ((forall x : nat, R x x) /\ (forall x : nat, forall y : nat, forall z : nat, ((R x y) /\ (R y z)) -> R x z)) -> (forall m : nat, forall n : nat, (Peano.le m n) -> R m n) = (forall n : nat, R n (S n)).
