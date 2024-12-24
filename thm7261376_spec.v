Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7261376 : forall (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : forall i : nat, ((Peano.le a i) /\ (Peano.le i b)) -> (f i) = (g i)), (@sum nat (dotdot a b) (fun i : nat => f i)) = (@sum nat (dotdot a b) g).
