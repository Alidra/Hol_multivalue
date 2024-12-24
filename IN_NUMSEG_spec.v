Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5371273 : forall m : nat, forall n : nat, forall p : nat, (@IN nat p (dotdot m n)) = ((Peano.le m p) /\ (Peano.le p n)).
