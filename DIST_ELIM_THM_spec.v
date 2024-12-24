Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1246841 : forall (y : nat) (x : nat) (P : nat -> Prop), (P (dist (@pair nat nat x y))) = (forall d : nat, ((x = (Nat.add y d)) -> P d) /\ ((y = (Nat.add x d)) -> P d)).
