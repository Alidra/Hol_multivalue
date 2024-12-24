Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 := fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term32 (x0 : int) := @eq Prop (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)).
Definition term22 (x0 : int) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term3 := int_of_num (NUMERAL 0).
Definition term30 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term27 := fun y0 : int => True.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, ((rem y0 y1) = (int_of_num (NUMERAL 0))) = (int_divides y1 y0)) x0.
Definition term21 := (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) /\ (forall y0 : int, (~ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0))).
Definition term20 := (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) /\ (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0))).
Definition term10 := forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))).
Definition term14 (x0 : int) := ~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term18 := forall y0 : int, (~ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term28 := forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => ((rem x0 y0) = (int_of_num (NUMERAL 0))) = (int_divides y0 x0)) x1.
Definition term17 := forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term12 (x0 : int) := @eq Prop ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term31 (x0 : Prop) := forall y0 : int, x0.
Definition term6 (x0 : int) := rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term8 := fun y0 : int => (~ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term9 := fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))).
Definition term26 := fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term16 := fun y0 : int => (~ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term29 := forall y0 : int, True.
Definition term19 := and (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term13 (x0 : int) := @eq Prop (~ ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))).
Definition term11 (x0 : int) := (fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))))) x0.
Definition term23 := int_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term5 (x0 : int) := ~ ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term1 (x0 : int) := forall y0 : int, ((rem x0 y0) = (int_of_num (NUMERAL 0))) = (int_divides y0 x0).
Definition term25 (x0 : int) := @eq Prop (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term24 (x0 : int) := @eq Prop ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term7 := int_of_num (NUMERAL (BIT1 0)).
Definition term4 := forall y0 : int, (~ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
