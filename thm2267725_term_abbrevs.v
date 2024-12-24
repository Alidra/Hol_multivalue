Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term55 := (fun y0 : real -> Prop => y0 (@ε real y0)) (fun y0 : real => integer y0).
Definition term31 (x0 : nat) := real_neg (real_of_num x0).
Definition term20 := real_of_num (NUMERAL 0).
Definition term3 (a0 : Type') (x0 : a0) := exists y0 : a0, x0 = y0.
Definition term42 := or (exists y0 : nat, (real_of_num (NUMERAL 0)) = (real_of_num y0)).
Definition term46 := (exists y0 : nat, (real_of_num (NUMERAL 0)) = (real_of_num y0)) \/ (exists y0 : nat, (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y0))).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term40 := exists y0 : nat, (real_of_num (NUMERAL 0)) = (real_of_num y0).
Definition term43 := fun y0 : nat => (fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y1))) y0.
Definition term50 := True \/ (exists y0 : nat, (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y0))).
Definition term15 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term52 := fun y0 : real => integer y0.
Definition term49 (x0 : nat) := exists y0 : nat, x0 = y0.
Definition term5 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y0 = y1.
Definition term54 := fun y0 : real -> Prop => y0 (@ε real y0).
Definition term48 := exists y0 : nat, (NUMERAL 0) = y0.
Definition term51 := exists y0 : real, integer y0.
Definition term7 (a0 : Type') := forall y0 : a0, exists y1 : a0, y0 = y1.
Definition term6 (a0 : Type') := forall y0 : a0, exists y1 : a0, y1 = y0.
Definition term8 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y0 = y1) x0.
Definition term38 := fun y0 : nat => (fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y1)) y0.
Definition term32 (x0 : nat) := ((fun y0 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y0)) x0) \/ ((fun y0 : nat => (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y0))) x0).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (exists y1 : a0, (x0 y1) \/ (y0 y1)) = ((exists y1 : a0, x0 y1) \/ (exists y1 : a0, y0 y1)).
Definition term45 := exists y0 : nat, (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y0)).
Definition term37 := @eq Prop (exists y0 : nat, ((real_of_num (NUMERAL 0)) = (real_of_num y0)) \/ ((real_of_num (NUMERAL 0)) = (real_neg (real_of_num y0)))).
Definition term36 := @eq Prop (exists y0 : nat, ((fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y1))) y0)).
Definition term19 := exists y0 : nat, ((real_of_num (NUMERAL 0)) = (real_of_num y0)) \/ ((real_of_num (NUMERAL 0)) = (real_neg (real_of_num y0))).
Definition term24 := (exists y0 : nat, (fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y1))) y0).
Definition term35 := fun y0 : nat => ((real_of_num (NUMERAL 0)) = (real_of_num y0)) \/ ((real_of_num (NUMERAL 0)) = (real_neg (real_of_num y0))).
Definition term47 := fun y0 : nat => (NUMERAL 0) = y0.
Definition term53 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term25 := fun y0 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y0).
Definition term27 (x0 : nat) := (fun y0 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y0)) x0.
Definition term23 := exists y0 : nat, ((fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y1))) y0).
Definition term26 := fun y0 : nat => (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y0)).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (exists y2 : a0, (y0 y2) \/ (y1 y2)) = ((exists y2 : a0, y0 y2) \/ (exists y2 : a0, y1 y2))) x0.
Definition term28 (x0 : nat) := or ((fun y0 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y0)) x0).
Definition term2 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term4 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y1 = y0.
Definition term44 := exists y0 : nat, (fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y1))) y0.
Definition term39 := exists y0 : nat, (fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y1)) y0.
Definition term0 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term18 := integer (real_of_num (NUMERAL 0)).
Definition term33 (x0 : nat) := ((real_of_num (NUMERAL 0)) = (real_of_num x0)) \/ ((real_of_num (NUMERAL 0)) = (real_neg (real_of_num x0))).
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term30 (x0 : nat) := (fun y0 : nat => (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y0))) x0.
Definition term29 (x0 : nat) := or ((real_of_num (NUMERAL 0)) = (real_of_num x0)).
Definition term17 (x0 : real) := exists y0 : nat, (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0))).
Definition term21 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term1 (a0 : Type') (x0 : a0) := fun y0 : a0 => x0 = y0.
Definition term34 := fun y0 : nat => ((fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_neg (real_of_num y1))) y0).
Definition term41 := or (exists y0 : nat, (fun y1 : nat => (real_of_num (NUMERAL 0)) = (real_of_num y1)) y0).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0, (x0 y1) \/ (y0 y1)) = ((exists y1 : a0, x0 y1) \/ (exists y1 : a0, y0 y1))) x1.
Definition term56 := (fun y0 : real => integer y0) (@ε real (fun y0 : real => integer y0)).
Definition term22 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
