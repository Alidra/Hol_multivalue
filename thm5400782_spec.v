Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5400782 : forall (m : nat) (p : nat) (n : nat), ((fun p' : nat => (@IN nat p' (dotdot m n)) = ((Peano.le m p') /\ (Peano.le p' n))) p) = ((@IN nat p (dotdot m n)) = ((Peano.le m p) /\ (Peano.le p n))).
