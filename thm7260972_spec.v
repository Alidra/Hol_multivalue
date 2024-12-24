Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7260972 : forall (f : nat -> real) (a : nat) (b : nat) (g : nat -> real), (forall x : nat, (@IN nat x (dotdot a b)) -> ((fun i : nat => f i) x) = (g x)) -> (@sum nat (dotdot a b) (fun i : nat => f i)) = (@sum nat (dotdot a b) g).
