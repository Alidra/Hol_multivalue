Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7261462 : forall (f : nat -> real) (a : nat) (b : nat) (g : nat -> real), ((fun b' : nat => (forall i : nat, ((Peano.le a i) /\ (Peano.le i b')) -> (f i) = (g i)) -> (@sum nat (dotdot a b') (fun i : nat => f i)) = (@sum nat (dotdot a b') g)) b) = ((forall i : nat, ((Peano.le a i) /\ (Peano.le i b)) -> (f i) = (g i)) -> (@sum nat (dotdot a b) (fun i : nat => f i)) = (@sum nat (dotdot a b) g)).
