Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term3 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) = (Peano.lt (NUMERAL 0) y0).
Definition term8 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) = (Peano.lt (NUMERAL 0) y0)) x0.
Definition term7 (x0 : nat) := Peano.lt (NUMERAL 0) (Factorial.fact x0).
Definition term1 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term12 := forall y0 : nat, ~ ((Factorial.fact y0) = (NUMERAL 0)).
Definition term2 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term10 := fun y0 : nat => ~ ((Factorial.fact y0) = (NUMERAL 0)).
Definition term13 := forall y0 : nat, True.
Definition term11 := fun y0 : nat => True.
Definition term4 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term9 (x0 : nat) := ~ ((Factorial.fact x0) = (NUMERAL 0)).
Definition term15 (x0 : Prop) := forall y0 : nat, x0.
Definition term5 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) = (Peano.lt (NUMERAL 0) y0).
Definition term6 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) x0.
Definition term0 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
