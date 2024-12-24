Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7041096 : forall f : nat -> nat, forall g : nat -> nat, forall m : nat, forall n : nat, (forall i : nat, ((Peano.le m i) /\ (Peano.le i n)) -> Peano.le (f i) (g i)) -> Peano.le (@nsum nat (dotdot m n) f) (@nsum nat (dotdot m n) g).
