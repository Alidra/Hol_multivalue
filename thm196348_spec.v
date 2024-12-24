Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem196348 : (forall m : nat, forall n : nat, (~ (n = (NUMERAL 0))) -> ((Nat.div m n) = (NUMERAL 0)) = (Peano.lt m n)) = (forall m : nat, forall n : nat, (~ (n = (NUMERAL 0))) -> ((Nat.div m n) = (NUMERAL 0)) = (Peano.lt m n)).
