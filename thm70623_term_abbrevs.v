Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : ind) := fun y0 : ind => ((IND_SUC x0) = (IND_SUC y0)) = (x0 = y0).
Definition term1 := (exists y0 : ind -> ind, exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1))) -> (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1))) (@ε (ind -> ind) (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1)))).
Definition term31 := exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0)).
Definition term4 := exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((@ε (ind -> ind) (fun y3 : ind -> ind => exists y4 : ind, (forall y5 : ind, forall y6 : ind, ((y3 y5) = (y3 y6)) = (y5 = y6)) /\ (forall y5 : ind, ~ ((y3 y5) = y4))) y1) = (@ε (ind -> ind) (fun y3 : ind -> ind => exists y4 : ind, (forall y5 : ind, forall y6 : ind, ((y3 y5) = (y3 y6)) = (y5 = y6)) /\ (forall y5 : ind, ~ ((y3 y5) = y4))) y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((@ε (ind -> ind) (fun y2 : ind -> ind => exists y3 : ind, (forall y4 : ind, forall y5 : ind, ((y2 y4) = (y2 y5)) = (y4 = y5)) /\ (forall y4 : ind, ~ ((y2 y4) = y3))) y1) = y0)).
Definition term28 (x0 : ind) := (forall y0 : ind, forall y1 : ind, ((IND_SUC y0) = (IND_SUC y1)) = (y0 = y1)) /\ (forall y0 : ind, ~ ((IND_SUC y0) = x0)).
Definition term27 (x0 : ind) := (forall y0 : ind, forall y1 : ind, ((@ε (ind -> ind) (fun y2 : ind -> ind => exists y3 : ind, (forall y4 : ind, forall y5 : ind, ((y2 y4) = (y2 y5)) = (y4 = y5)) /\ (forall y4 : ind, ~ ((y2 y4) = y3))) y0) = (@ε (ind -> ind) (fun y2 : ind -> ind => exists y3 : ind, (forall y4 : ind, forall y5 : ind, ((y2 y4) = (y2 y5)) = (y4 = y5)) /\ (forall y4 : ind, ~ ((y2 y4) = y3))) y1)) = (y0 = y1)) /\ (forall y0 : ind, ~ ((@ε (ind -> ind) (fun y1 : ind -> ind => exists y2 : ind, (forall y3 : ind, forall y4 : ind, ((y1 y3) = (y1 y4)) = (y3 = y4)) /\ (forall y3 : ind, ~ ((y1 y3) = y2))) y0) = x0)).
Definition term16 := fun y0 : ind => forall y1 : ind, ((IND_SUC y0) = (IND_SUC y1)) = (y0 = y1).
Definition term15 := fun y0 : ind => forall y1 : ind, ((@ε (ind -> ind) (fun y2 : ind -> ind => exists y3 : ind, (forall y4 : ind, forall y5 : ind, ((y2 y4) = (y2 y5)) = (y4 = y5)) /\ (forall y4 : ind, ~ ((y2 y4) = y3))) y0) = (@ε (ind -> ind) (fun y2 : ind -> ind => exists y3 : ind, (forall y4 : ind, forall y5 : ind, ((y2 y4) = (y2 y5)) = (y4 = y5)) /\ (forall y4 : ind, ~ ((y2 y4) = y3))) y1)) = (y0 = y1).
Definition term2 := fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1)).
Definition term23 (x0 : ind) := fun y0 : ind => ~ ((@ε (ind -> ind) (fun y1 : ind -> ind => exists y2 : ind, (forall y3 : ind, forall y4 : ind, ((y1 y3) = (y1 y4)) = (y3 = y4)) /\ (forall y3 : ind, ~ ((y1 y3) = y2))) y0) = x0).
Definition term7 (x0 : ind) := @eq ind (@ε (ind -> ind) (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1))) x0).
Definition term9 (x0 : ind) (x1 : ind) := @eq Prop ((@ε (ind -> ind) (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1))) x0) = (@ε (ind -> ind) (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1))) x1)).
Definition term11 (x0 : ind) := fun y0 : ind => ((@ε (ind -> ind) (fun y1 : ind -> ind => exists y2 : ind, (forall y3 : ind, forall y4 : ind, ((y1 y3) = (y1 y4)) = (y3 = y4)) /\ (forall y3 : ind, ~ ((y1 y3) = y2))) x0) = (@ε (ind -> ind) (fun y1 : ind -> ind => exists y2 : ind, (forall y3 : ind, forall y4 : ind, ((y1 y3) = (y1 y4)) = (y3 = y4)) /\ (forall y3 : ind, ~ ((y1 y3) = y2))) y0)) = (x0 = y0).
Definition term5 := @ε (ind -> ind) (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1))).
Definition term14 (x0 : ind) := forall y0 : ind, ((IND_SUC x0) = (IND_SUC y0)) = (x0 = y0).
Definition term13 (x0 : ind) := forall y0 : ind, ((@ε (ind -> ind) (fun y1 : ind -> ind => exists y2 : ind, (forall y3 : ind, forall y4 : ind, ((y1 y3) = (y1 y4)) = (y3 = y4)) /\ (forall y3 : ind, ~ ((y1 y3) = y2))) x0) = (@ε (ind -> ind) (fun y1 : ind -> ind => exists y2 : ind, (forall y3 : ind, forall y4 : ind, ((y1 y3) = (y1 y4)) = (y3 = y4)) /\ (forall y3 : ind, ~ ((y1 y3) = y2))) y0)) = (x0 = y0).
Definition term3 := (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1))) (@ε (ind -> ind) (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1)))).
Definition term8 (x0 : ind) := @eq ind (IND_SUC x0).
Definition term0 (x0 : type922) := (ex x0) -> x0 (@ε (ind -> ind) x0).
Definition term22 (x0 : ind) (x1 : ind) := ~ ((IND_SUC x0) = x1).
Definition term10 (x0 : ind) (x1 : ind) := @eq Prop ((IND_SUC x0) = (IND_SUC x1)).
Definition term26 (x0 : ind) := forall y0 : ind, ~ ((IND_SUC y0) = x0).
Definition term25 (x0 : ind) := forall y0 : ind, ~ ((@ε (ind -> ind) (fun y1 : ind -> ind => exists y2 : ind, (forall y3 : ind, forall y4 : ind, ((y1 y3) = (y1 y4)) = (y3 = y4)) /\ (forall y3 : ind, ~ ((y1 y3) = y2))) y0) = x0).
Definition term18 := forall y0 : ind, forall y1 : ind, ((IND_SUC y0) = (IND_SUC y1)) = (y0 = y1).
Definition term17 := forall y0 : ind, forall y1 : ind, ((@ε (ind -> ind) (fun y2 : ind -> ind => exists y3 : ind, (forall y4 : ind, forall y5 : ind, ((y2 y4) = (y2 y5)) = (y4 = y5)) /\ (forall y4 : ind, ~ ((y2 y4) = y3))) y0) = (@ε (ind -> ind) (fun y2 : ind -> ind => exists y3 : ind, (forall y4 : ind, forall y5 : ind, ((y2 y4) = (y2 y5)) = (y4 = y5)) /\ (forall y4 : ind, ~ ((y2 y4) = y3))) y1)) = (y0 = y1).
Definition term30 := fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0)).
Definition term29 := fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((@ε (ind -> ind) (fun y3 : ind -> ind => exists y4 : ind, (forall y5 : ind, forall y6 : ind, ((y3 y5) = (y3 y6)) = (y5 = y6)) /\ (forall y5 : ind, ~ ((y3 y5) = y4))) y1) = (@ε (ind -> ind) (fun y3 : ind -> ind => exists y4 : ind, (forall y5 : ind, forall y6 : ind, ((y3 y5) = (y3 y6)) = (y5 = y6)) /\ (forall y5 : ind, ~ ((y3 y5) = y4))) y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((@ε (ind -> ind) (fun y2 : ind -> ind => exists y3 : ind, (forall y4 : ind, forall y5 : ind, ((y2 y4) = (y2 y5)) = (y4 = y5)) /\ (forall y4 : ind, ~ ((y2 y4) = y3))) y1) = y0)).
Definition term6 (x0 : ind) := @ε (ind -> ind) (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1))) x0.
Definition term21 (x0 : ind) (x1 : ind) := ~ ((@ε (ind -> ind) (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1))) x0) = x1).
Definition term24 (x0 : ind) := fun y0 : ind => ~ ((IND_SUC y0) = x0).
Definition term20 := and (forall y0 : ind, forall y1 : ind, ((IND_SUC y0) = (IND_SUC y1)) = (y0 = y1)).
Definition term19 := and (forall y0 : ind, forall y1 : ind, ((@ε (ind -> ind) (fun y2 : ind -> ind => exists y3 : ind, (forall y4 : ind, forall y5 : ind, ((y2 y4) = (y2 y5)) = (y4 = y5)) /\ (forall y4 : ind, ~ ((y2 y4) = y3))) y0) = (@ε (ind -> ind) (fun y2 : ind -> ind => exists y3 : ind, (forall y4 : ind, forall y5 : ind, ((y2 y4) = (y2 y5)) = (y4 = y5)) /\ (forall y4 : ind, ~ ((y2 y4) = y3))) y1)) = (y0 = y1)).