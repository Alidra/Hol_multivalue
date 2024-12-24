Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem146697 : forall n : nat, forall x : nat, (Peano.lt (NUMERAL 0) (Nat.pow x n)) = ((~ (x = (NUMERAL 0))) \/ (n = (NUMERAL 0))).
