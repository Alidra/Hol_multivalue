Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := and (~ (x0 = (Nat.add x1 x2))).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (x0 = (Nat.add x1 x2))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (x2 = (NUMERAL 0))))).
Definition term17 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop (x0 (Nat.sub x1 x2)).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((~ (x0 = (Nat.add x1 y0))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x2 y0).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((x0 = (Nat.add x1 x2)) \/ ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0))))).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := (~ ((x0 = (Nat.add x1 x3)) \/ ((Peano.lt x0 x1) /\ (x3 = (NUMERAL 0))))) \/ (x2 x3).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (x2 = (NUMERAL 0)).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (Nat.add x1 x2))) /\ (~ ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0)))).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add x1 x2)) \/ ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0))).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((~ (x0 = (Nat.add x1 y0))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (y0 = (NUMERAL 0))))) \/ (x2 y0).
Definition term18 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := x0 (Nat.sub x1 x2).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0))).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x0 = (Nat.add x1 x2)) \/ ((Peano.lt x0 x1) /\ (x2 = (NUMERAL 0)))).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat => ((x0 = (Nat.add x1 y0)) \/ ((Peano.lt x0 x1) /\ (y0 = (NUMERAL 0)))) -> x2 y0.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (x2 = (NUMERAL 0))).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((x0 = (Nat.add x1 x3)) \/ ((Peano.lt x0 x1) /\ (x3 = (NUMERAL 0)))) -> x2 x3.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (Nat.add x1 x2))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (x2 = (NUMERAL 0)))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat) := ((~ (x0 = (Nat.add x1 x3))) /\ ((~ (Peano.lt x0 x1)) \/ (~ (x3 = (NUMERAL 0))))) \/ (x2 x3).
