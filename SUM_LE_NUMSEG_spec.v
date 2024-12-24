Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7210448 : forall f : nat -> real, forall g : nat -> real, forall m : nat, forall n : nat, (forall i : nat, ((Peano.le m i) /\ (Peano.le i n)) -> real_le (f i) (g i)) -> real_le (@sum nat (dotdot m n) f) (@sum nat (dotdot m n) g).
