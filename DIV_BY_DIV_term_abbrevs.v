Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) /\ (num_divides x0 x1).
Definition term37 (x0 : nat) (x1 : nat) := imp ((~ (x1 = (NUMERAL 0))) /\ (num_divides x0 x1)).
Definition term30 := int_of_num (NUMERAL 0).
Definition term1 (x0 : nat) (x1 : nat) := int_of_num (Nat.div x0 x1).
Definition term52 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term48 (x0 : nat) := fun y0 : nat => ((~ (y0 = (NUMERAL 0))) /\ (num_divides x0 y0)) -> (Nat.div y0 (Nat.div y0 x0)) = x0.
Definition term40 (x0 : nat) (x1 : nat) := int_of_num (Nat.div x0 (Nat.div x0 x1)).
Definition term18 (x0 : int) := (fun y0 : int => forall y1 : int, ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (int_divides y0 y1)) -> (div y1 (div y1 y0)) = y0) x0.
Definition term12 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term44 (x0 : nat) (x1 : nat) := @eq int (int_of_num (Nat.div x0 (Nat.div x0 x1))).
Definition term34 (x0 : nat) := and (~ ((int_of_num x0) = (int_of_num (NUMERAL 0)))).
Definition term10 (x0 : nat) := fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) = ((int_of_num x0) = (int_of_num y0))) x1.
Definition term31 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term54 := fun y0 : nat => forall y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ (num_divides y0 y1)) -> (Nat.div y1 (Nat.div y1 y0)) = y0.
Definition term14 := fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1).
Definition term3 (x0 : nat) := fun y0 : nat => (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0)).
Definition term36 (x0 : nat) (x1 : nat) := (~ ((int_of_num x1) = (int_of_num (NUMERAL 0)))) /\ (int_divides (int_of_num x0) (int_of_num x1)).
Definition term0 (x0 : nat) (x1 : nat) := div (int_of_num x0) (int_of_num x1).
Definition term32 (x0 : nat) := ~ ((int_of_num x0) = (int_of_num (NUMERAL 0))).
Definition term42 (x0 : nat) := div (int_of_num x0).
Definition term50 (x0 : nat) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) /\ (num_divides x0 y0)) -> (Nat.div y0 (Nat.div y0 x0)) = x0.
Definition term39 (x0 : nat) (x1 : nat) := Nat.div x0 (Nat.div x0 x1).
Definition term55 := forall y0 : nat, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ (num_divides y0 y1)) -> (Nat.div y1 (Nat.div y1 y0)) = y0.
Definition term17 := forall y0 : nat, forall y1 : nat, (y0 = y1) = ((int_of_num y0) = (int_of_num y1)).
Definition term16 := forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1).
Definition term9 := forall y0 : nat, forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1)).
Definition term8 := forall y0 : nat, forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1)).
Definition term21 (x0 : int) (x1 : int) := ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (int_divides x1 x0)) -> (div x0 (div x0 x1)) = x1.
Definition term5 (x0 : nat) := forall y0 : nat, (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0)).
Definition term51 := forall y0 : nat, True.
Definition term2 (x0 : nat) := fun y0 : nat => (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term49 := fun y0 : nat => True.
Definition term4 (x0 : nat) := forall y0 : nat, (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term33 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term45 (x0 : nat) (x1 : nat) := @eq int (div (int_of_num x0) (div (int_of_num x0) (int_of_num x1))).
Definition term43 (x0 : nat) (x1 : nat) := div (int_of_num x0) (div (int_of_num x0) (int_of_num x1)).
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0))) x1.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) = ((int_of_num y0) = (int_of_num y1))) x0.
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1))) x0.
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (num_divides y0 y1) = (int_divides (int_of_num y0) (int_of_num y1))) x0.
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => (num_divides x0 y0) = (int_divides (int_of_num x0) (int_of_num y0))) x1.
Definition term11 (x0 : nat) := fun y0 : nat => (x0 = y0) = ((int_of_num x0) = (int_of_num y0)).
Definition term47 (x0 : nat) (x1 : nat) := ((~ ((int_of_num x0) = (int_of_num (NUMERAL 0)))) /\ (int_divides (int_of_num x1) (int_of_num x0))) -> (div (int_of_num x0) (div (int_of_num x0) (int_of_num x1))) = (int_of_num x1).
Definition term19 (x0 : int) := forall y0 : int, ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (int_divides x0 y0)) -> (div y0 (div y0 x0)) = x0.
Definition term23 (x0 : nat) := forall y0 : nat, (num_divides x0 y0) = (int_divides (int_of_num x0) (int_of_num y0)).
Definition term13 (x0 : nat) := forall y0 : nat, (x0 = y0) = ((int_of_num x0) = (int_of_num y0)).
Definition term53 (x0 : Prop) := forall y0 : nat, x0.
Definition term41 (x0 : nat) (x1 : nat) := div (int_of_num x0) (int_of_num (Nat.div x0 x1)).
Definition term6 := fun y0 : nat => forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1)).
Definition term20 (x0 : int) (x1 : int) := (fun y0 : int => ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (int_divides x0 y0)) -> (div y0 (div y0 x0)) = x0) x1.
Definition term38 (x0 : nat) (x1 : nat) := imp ((~ ((int_of_num x1) = (int_of_num (NUMERAL 0)))) /\ (int_divides (int_of_num x0) (int_of_num x1))).
Definition term15 := fun y0 : nat => forall y1 : nat, (y0 = y1) = ((int_of_num y0) = (int_of_num y1)).
Definition term7 := fun y0 : nat => forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1)).
Definition term46 (x0 : nat) (x1 : nat) := ((~ (x0 = (NUMERAL 0))) /\ (num_divides x1 x0)) -> (Nat.div x0 (Nat.div x0 x1)) = x1.
Definition term25 (x0 : nat) (x1 : nat) := int_divides (int_of_num x0) (int_of_num x1).
