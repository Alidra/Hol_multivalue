Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : type1400 a0) := @ε a0 (fun y0 : a0 => forall y1 : a0, ((x0 y0 y1) = y1) /\ ((x0 y1 y0) = y1)).
Definition term5 := @eq int (@ε int (fun y0 : int => forall y1 : int, ((int_mul y0 y1) = y1) /\ ((int_mul y1 y0) = y1))).
Definition term4 := @eq int (@neutral int int_mul).
Definition term0 (a0 : Type') (x0 : type1400 a0) := (fun y0 : type1400 a0 => (@neutral a0 y0) = (@ε a0 (fun y1 : a0 => forall y2 : a0, ((y0 y1 y2) = y2) /\ ((y0 y2 y1) = y2)))) x0.
Definition term6 := int_of_num (NUMERAL (BIT1 0)).
Definition term3 := @ε int (fun y0 : int => forall y1 : int, ((int_mul y0 y1) = y1) /\ ((int_mul y1 y0) = y1)).
Definition term2 (x0 : type1551) := @ε int (fun y0 : int => forall y1 : int, ((x0 y0 y1) = y1) /\ ((x0 y1 y0) = y1)).
