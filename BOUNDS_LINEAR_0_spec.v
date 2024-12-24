Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1260600 : forall A : nat, forall B : nat, (forall n : nat, Peano.le (Nat.mul A n) B) = (A = (NUMERAL 0)).
