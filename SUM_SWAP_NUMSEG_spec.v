Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7222072 : forall a : nat, forall b : nat, forall c : nat, forall d : nat, forall f : nat -> nat -> real, (@sum nat (dotdot a b) (fun i : nat => @sum nat (dotdot c d) (f i))) = (@sum nat (dotdot c d) (fun j : nat => @sum nat (dotdot a b) (fun i : nat => f i j))).
