Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem191396 : forall a : nat, forall b : nat, forall n : nat, ((~ (a = (NUMERAL 0))) /\ (Peano.le b (Nat.mul a n))) -> Peano.le (Nat.div b a) n.
