Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5476933 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, (@SUBSET nat (dotdot m n) (dotdot p q)) = ((Peano.lt n m) \/ ((Peano.le p m) /\ (Peano.le n q))).
