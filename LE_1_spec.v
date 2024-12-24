Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem99082 : (forall n : nat, (~ (n = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) n) /\ ((forall n : nat, (~ (n = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) n) /\ ((forall n : nat, (Peano.lt (NUMERAL 0) n) -> ~ (n = (NUMERAL 0))) /\ ((forall n : nat, (Peano.lt (NUMERAL 0) n) -> Peano.le (NUMERAL (BIT1 0)) n) /\ ((forall n : nat, (Peano.le (NUMERAL (BIT1 0)) n) -> Peano.lt (NUMERAL 0) n) /\ (forall n : nat, (Peano.le (NUMERAL (BIT1 0)) n) -> ~ (n = (NUMERAL 0))))))).
