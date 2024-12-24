Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5451441 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, (@DISJOINT nat (dotdot m n) (dotdot p q)) = ((Peano.lt n p) \/ ((Peano.lt q m) \/ ((Peano.lt n m) \/ (Peano.lt q p)))).
