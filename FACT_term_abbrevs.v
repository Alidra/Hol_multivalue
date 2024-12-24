Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, (Factorial.fact (S y0)) = (Nat.mul (S y0) (Factorial.fact y0)).
Definition term3 := ((Factorial.fact (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, (Factorial.fact (S y0)) = (Nat.mul (S y0) (Factorial.fact y0))).
Definition term1 := Factorial.fact (NUMERAL 0).
Definition term2 := NUMERAL (BIT1 0).
