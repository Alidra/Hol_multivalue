Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term181 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term132 (x0 : real) (x1 : real) := fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0) (real_of_num (NUMERAL 0))).
Definition term159 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term54 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_max x1 x0) (real_max x0 x1)) (real_of_num (NUMERAL 0))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term36 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term55 (x0 : real) (x1 : real) := or (real_gt (real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))) (real_of_num (NUMERAL 0))).
Definition term162 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term52 (x0 : real) (x1 : real) := real_gt (real_sub (real_max x1 x0) (real_max x0 x1)) (real_of_num (NUMERAL 0)).
Definition term106 := (exists y0 : real, exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0))).
Definition term138 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))) x1.
Definition term133 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0) (real_of_num (NUMERAL 0)))) x1.
Definition term47 := real_of_num (NUMERAL 0).
Definition term192 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term139 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term134 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1) (real_of_num (NUMERAL 0))).
Definition term51 (x0 : real) (x1 : real) := real_gt (real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))).
Definition term10 (x0 : real) := exists y0 : real, ~ ((real_max x0 y0) = (real_max y0 x0)).
Definition term131 (x0 : real) (x1 : real) := ((real_ge x0 x1) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0) (real_of_num (NUMERAL 0)))) x0)) \/ ((real_gt x1 x0) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0) (real_of_num (NUMERAL 0)))) x1)).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term111 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x1 x2))) x3.
Definition term44 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_max x1 x0) (real_max x0 x1))).
Definition term175 (x0 : real) (x1 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term154 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term197 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term2 (x0 : real) := ~ (forall y0 : real, (real_max x0 y0) = (real_max y0 x0)).
Definition term142 (x0 : real) (x1 : real) := (real_ge x1 x0) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))).
Definition term45 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_max x1 x0) (real_max x0 x1))).
Definition term92 (x0 : real) := or ((fun y0 : real => exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))) x0).
Definition term15 (x0 : real) := forall y0 : real, (real_max x0 y0) = (real_max y0 x0).
Definition term213 (x0 : real) (x1 : real) := or (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))))).
Definition term190 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term5 (x0 : real) (x1 : real) := (fun y0 : real => (real_max x0 y0) = (real_max y0 x0)) x1.
Definition term6 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_max x0 y0) = (real_max y0 x0)) x1).
Definition term21 (x0 : real) (x1 : real) := real_sub (real_max x1 x0) (real_max x0 x1).
Definition term152 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term28 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1).
Definition term29 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1)).
Definition term179 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term123 (x0 : real) (x1 : real) := real_gt (real_add (real_max x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term210 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term149 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term166 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term176 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term49 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x1 x0)) (real_max x0 x1)) (real_of_num (NUMERAL 0)).
Definition term212 (x0 : real) (x1 : real) := ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term202 (x0 : real) (x1 : real) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term211 (x0 : real) (x1 : real) := or ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))))).
Definition term201 (x0 : real) (x1 : real) := or ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))).
Definition term82 (x0 : real) := exists y0 : real, (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1)) (real_max y1 x0)) (real_of_num (NUMERAL 0))) y0.
Definition term77 (x0 : real) := exists y0 : real, (fun y1 : real => real_gt (real_add (real_max x0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 x0))) (real_of_num (NUMERAL 0))) y0.
Definition term214 (x0 : real) (x1 : real) := (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))))) \/ (((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))))).
Definition term167 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term219 := forall y0 : real, forall y1 : real, (real_max y0 y1) = (real_max y1 y0).
Definition term129 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_max x0 x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_max x0 x1)) (real_of_num (NUMERAL 0))).
Definition term113 (x0 : real) (x1 : real) := (real_gt (real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term105 := exists y0 : real, exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0)).
Definition term100 := exists y0 : real, exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0)).
Definition term60 := exists y0 : real, exists y1 : real, (real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0))).
Definition term19 := exists y0 : real, exists y1 : real, ~ ((real_max y0 y1) = (real_max y1 y0)).
Definition term33 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term101 := or (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_max y1 y2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y2 y1))) (real_of_num (NUMERAL 0))) y0).
Definition term79 (x0 : real) := or (exists y0 : real, (fun y1 : real => real_gt (real_add (real_max x0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 x0))) (real_of_num (NUMERAL 0))) y0).
Definition term124 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_max x0 x1)).
Definition term12 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_max y1 y2) = (real_max y2 y1)) y0).
Definition term3 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_max x0 y1) = (real_max y1 x0)) y0).
Definition term93 (x0 : real) := (fun y0 : real => exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0))) x0.
Definition term91 (x0 : real) := (fun y0 : real => exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))) x0.
Definition term112 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) x3) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) x3).
Definition term126 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_max x0 x1)) (real_of_num (NUMERAL 0)).
Definition term120 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_max x0 x1)) (real_of_num (NUMERAL 0)).
Definition term130 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))) (real_max x0 x1).
Definition term189 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term151 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term30 (x0 : real) (x1 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_max x0 x1).
Definition term114 (x0 : real) (x1 : real) := real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term17 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_max y1 y2) = (real_max y2 y1)) y0).
Definition term42 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1)).
Definition term71 (x0 : real) (x1 : real) := (fun y0 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0)) (real_max y0 x0)) (real_of_num (NUMERAL 0))) x1.
Definition term90 := fun y0 : real => exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0)).
Definition term89 := fun y0 : real => exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0)).
Definition term183 := and (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term205 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term118 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_max x0 x1)).
Definition term94 (x0 : real) := ((fun y0 : real => exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0))) x0).
Definition term157 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term37 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term46 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x1 x0)) (real_max x0 x1)).
Definition term41 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_max x0 x1).
Definition term67 (x0 : real) := fun y0 : real => real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0)).
Definition term20 (x0 : real) (x1 : real) := (real_gt (real_sub (real_max x1 x0) (real_max x0 x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_max x1 x0) (real_max x0 x1))) (real_of_num (NUMERAL 0))).
Definition term63 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term84 (x0 : real) := (exists y0 : real, real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0)) (real_max y0 x0)) (real_of_num (NUMERAL 0))).
Definition term11 := ~ (forall y0 : real, forall y1 : real, (real_max y0 y1) = (real_max y1 y0)).
Definition term216 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term168 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term143 (x0 : real) (x1 : real) := or ((real_ge x1 x0) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))) x1)).
Definition term125 (x0 : real) (x1 : real) := real_gt (real_add (real_max x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term119 (x0 : real) (x1 : real) := real_gt (real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term146 (x0 : real) (x1 : real) := @eq Prop ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_max x0 x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_max x0 x1)) (real_of_num (NUMERAL 0)))).
Definition term163 := real_sub (real_of_num (NUMERAL 0)).
Definition term83 (x0 : real) := exists y0 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0)) (real_max y0 x0)) (real_of_num (NUMERAL 0)).
Definition term78 (x0 : real) := exists y0 : real, real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0)).
Definition term140 (x0 : real) (x1 : real) := and (real_ge x0 x1).
Definition term103 := fun y0 : real => (fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2)) (real_max y2 y1)) (real_of_num (NUMERAL 0))) y0.
Definition term98 := fun y0 : real => (fun y1 : real => exists y2 : real, real_gt (real_add (real_max y1 y2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y2 y1))) (real_of_num (NUMERAL 0))) y0.
Definition term186 (x0 : real) (x1 : real) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))).
Definition term50 (x0 : real) (x1 : real) := real_gt (real_sub (real_max x1 x0) (real_max x0 x1)).
Definition term64 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term48 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_max x1 x0) (real_max x0 x1))) (real_of_num (NUMERAL 0)).
Definition term173 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term200 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term16 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_max y0 y1) = (real_max y1 y0)) x0).
Definition term59 := fun y0 : real => exists y1 : real, (real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0))).
Definition term22 (x0 : real) (x1 : real) := real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1)).
Definition term198 (x0 : real) (x1 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term122 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_max x0 x1).
Definition term155 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term39 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term164 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term97 := @eq Prop (exists y0 : real, (exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))) \/ (exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0)))).
Definition term96 := @eq Prop (exists y0 : real, ((fun y1 : real => exists y2 : real, real_gt (real_add (real_max y1 y2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y2 y1))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2)) (real_max y2 y1)) (real_of_num (NUMERAL 0))) y0)).
Definition term75 (x0 : real) := @eq Prop (exists y0 : real, (real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0)) (real_max y0 x0)) (real_of_num (NUMERAL 0)))).
Definition term74 (x0 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_add (real_max x0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 x0))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1)) (real_max y1 x0)) (real_of_num (NUMERAL 0))) y0)).
Definition term206 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term13 := fun y0 : real => forall y1 : real, (real_max y0 y1) = (real_max y1 y0).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term57 (x0 : real) := fun y0 : real => (real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0)) (real_max y0 x0)) (real_of_num (NUMERAL 0))).
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : real, (real_max y0 y1) = (real_max y1 y0)) x0.
Definition term215 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term141 (x0 : real) (x1 : real) := (real_ge x1 x0) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))) x1).
Definition term4 (x0 : real) := fun y0 : real => (real_max x0 y0) = (real_max y0 x0).
Definition term204 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term145 (x0 : real) (x1 : real) := ((real_ge x0 x1) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt x1 x0) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1) (real_of_num (NUMERAL 0))))).
Definition term156 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term27 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term196 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term209 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term217 := (~ (forall y0 : real, forall y1 : real, (real_max y0 y1) = (real_max y1 y0))) -> False.
Definition term191 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term185 (x0 : real) (x1 : real) := and (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term150 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1).
Definition term182 (x0 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))).
Definition term115 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_max x0 x1).
Definition term128 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_max x0 x1)) (real_of_num (NUMERAL 0))).
Definition term127 (x0 : real) (x1 : real) := and (real_gt (real_add (real_max x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term160 := real_mul (real_of_num (NUMERAL 0)).
Definition term23 (x0 : real) (x1 : real) := real_neg (real_sub (real_max x1 x0) (real_max x0 x1)).
Definition term56 (x0 : real) (x1 : real) := (real_gt (real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x1 x0)) (real_max x0 x1)) (real_of_num (NUMERAL 0))).
Definition term116 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term180 (x0 : real) (x1 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term193 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term18 := fun y0 : real => exists y1 : real, ~ ((real_max y0 y1) = (real_max y1 y0)).
Definition term40 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term73 (x0 : real) := fun y0 : real => ((fun y1 : real => real_gt (real_add (real_max x0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 x0))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1)) (real_max y1 x0)) (real_of_num (NUMERAL 0))) y0).
Definition term87 := exists y0 : real, ((fun y1 : real => exists y2 : real, real_gt (real_add (real_max y1 y2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y2 y1))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2)) (real_max y2 y1)) (real_of_num (NUMERAL 0))) y0).
Definition term65 (x0 : real) := exists y0 : real, ((fun y1 : real => real_gt (real_add (real_max x0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 x0))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1)) (real_max y1 x0)) (real_of_num (NUMERAL 0))) y0).
Definition term194 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term218 := ((~ (forall y0 : real, forall y1 : real, (real_max y0 y1) = (real_max y1 y0))) -> False) -> forall y0 : real, forall y1 : real, (real_max y0 y1) = (real_max y1 y0).
Definition term53 (x0 : real) (x1 : real) := real_gt (real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))) (real_of_num (NUMERAL 0)).
Definition term187 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term31 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term195 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term135 (x0 : real) (x1 : real) := and (real_gt x0 x1).
Definition term70 (x0 : real) (x1 : real) := or ((fun y0 : real => real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0))) x1).
Definition term199 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term34 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term7 (x0 : real) (x1 : real) := ~ ((real_max x1 x0) = (real_max x0 x1)).
Definition term38 := real_of_num (NUMERAL (BIT1 0)).
Definition term26 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x1 x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))).
Definition term81 (x0 : real) := fun y0 : real => (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1)) (real_max y1 x0)) (real_of_num (NUMERAL 0))) y0.
Definition term76 (x0 : real) := fun y0 : real => (fun y1 : real => real_gt (real_add (real_max x0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 x0))) (real_of_num (NUMERAL 0))) y0.
Definition term72 (x0 : real) (x1 : real) := ((fun y0 : real => real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0))) x1) \/ ((fun y0 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0)) (real_max y0 x0)) (real_of_num (NUMERAL 0))) x1).
Definition term161 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term69 (x0 : real) (x1 : real) := (fun y0 : real => real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0))) x1.
Definition term136 (x0 : real) (x1 : real) := (real_gt x1 x0) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) y0) (real_of_num (NUMERAL 0)))) x1).
Definition term153 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term9 (x0 : real) := fun y0 : real => ~ ((real_max x0 y0) = (real_max y0 x0)).
Definition term144 (x0 : real) (x1 : real) := or ((real_ge x1 x0) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))).
Definition term8 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_max x0 y1) = (real_max y1 x0)) y0).
Definition term43 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x1 x0)) (real_max x0 x1).
Definition term207 (x0 : real) (x1 : real) := and (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term32 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term177 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term170 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term208 (x0 : real) (x1 : real) := (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))).
Definition term137 (x0 : real) (x1 : real) := (real_gt x1 x0) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1) (real_of_num (NUMERAL 0)))).
Definition term148 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term158 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term86 := exists y0 : real, (exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))) \/ (exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0))).
Definition term117 (x0 : real) (x1 : real) := real_gt (real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term24 (x0 : real) (x1 : real) := real_neg (real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))).
Definition term25 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_max x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))).
Definition term95 := fun y0 : real => ((fun y1 : real => exists y2 : real, real_gt (real_add (real_max y1 y2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y2 y1))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2)) (real_max y2 y1)) (real_of_num (NUMERAL 0))) y0).
Definition term188 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term203 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1)) x2) x3.
Definition term169 := real_add (real_of_num (NUMERAL 0)).
Definition term80 (x0 : real) := or (exists y0 : real, real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0))).
Definition term102 := or (exists y0 : real, exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term121 (x0 : real) (x1 : real) := real_add (real_max x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term171 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))).
Definition term174 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term85 := fun y0 : real => (exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))) \/ (exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0))).
Definition term178 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term35 := NUMERAL (BIT1 0).
Definition term88 := (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_max y1 y2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y2 y1))) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2)) (real_max y2 y1)) (real_of_num (NUMERAL 0))) y0).
Definition term66 (x0 : real) := (exists y0 : real, (fun y1 : real => real_gt (real_add (real_max x0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 x0))) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1)) (real_max y1 x0)) (real_of_num (NUMERAL 0))) y0).
Definition term165 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term58 (x0 : real) := exists y0 : real, (real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0)) (real_max y0 x0)) (real_of_num (NUMERAL 0))).
Definition term68 (x0 : real) := fun y0 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0)) (real_max y0 x0)) (real_of_num (NUMERAL 0)).
Definition term104 := exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2)) (real_max y2 y1)) (real_of_num (NUMERAL 0))) y0.
Definition term99 := exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_max y1 y2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y2 y1))) (real_of_num (NUMERAL 0))) y0.
Definition term184 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term147 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term172 := real_gt (real_of_num (NUMERAL 0)).
Definition term110 (x0 : real) := @eq Prop ((exists y0 : real, real_gt (real_add (real_max x0 y0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 x0))) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0)) (real_max y0 x0)) (real_of_num (NUMERAL 0)))).
Definition term109 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => real_gt (real_add (real_max x0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 x0))) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1)) (real_max y1 x0)) (real_of_num (NUMERAL 0))) y0)).
Definition term108 := @eq Prop ((exists y0 : real, exists y1 : real, real_gt (real_add (real_max y0 y1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y0))) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, exists y1 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1)) (real_max y1 y0)) (real_of_num (NUMERAL 0)))).
Definition term107 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_max y1 y2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y2 y1))) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2)) (real_max y2 y1)) (real_of_num (NUMERAL 0))) y0)).
