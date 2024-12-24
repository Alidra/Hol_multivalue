Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7261442 : forall f : nat -> real, forall g : nat -> real, forall a : nat, forall b : nat, (forall i : nat, ((Peano.le a i) /\ (Peano.le i b)) -> (f i) = (g i)) -> (@sum nat (dotdot a b) (fun i : nat => f i)) = (@sum nat (dotdot a b) g).
