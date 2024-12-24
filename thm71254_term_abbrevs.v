Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : ind -> Prop) (x1 : ind) := (((x1 = IND_0) -> x0 x1) -> (x1 = IND_0) -> x0 x1) /\ (((x1 = IND_0) -> x0 x1) -> (x1 = IND_0) -> x0 x1).
Definition term58 (x0 : ind -> Prop) (x1 : ind) := (fun y0 : ind => (x0 y0) = (forall y1 : ind -> Prop, (forall y2 : ind, ((y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y1 y3))) -> y1 y2) -> y1 y0)) x1.
Definition term43 (x0 : ind -> Prop) (x1 : ind) := ((forall y0 : ind, (y0 = IND_0) -> x0 y0) /\ (forall y0 : ind, (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0)) -> x0 x1.
Definition term127 (x0 : ind) (x1 : ind -> Prop) (x2 : ind) := imp ((fun y0 : ind => (x0 = (IND_SUC y0)) /\ (x1 y0)) x2).
Definition term138 (x0 : ind) (x1 : ind -> Prop) := exists y0 : ind, (fun y1 : ind => (x0 = (IND_SUC y1)) /\ (x1 y1)) y0.
Definition term80 (x0 : ind -> Prop) (x1 : ind) := imp ((fun y0 : ind => (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) x1).
Definition term16 (x0 : ind) (x1 : ind -> Prop) (x2 : ind) := ((x2 = (IND_SUC x0)) /\ (x1 x0)) -> x1 x2.
Definition term15 (x0 : ind -> Prop) (x1 : ind) := x0 (IND_SUC x1).
Definition term98 (x0 : ind -> Prop) := fun y0 : ind => ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> x0 y0.
Definition term19 (x0 : ind -> Prop) (x1 : ind) := (fun y0 : ind => forall y1 : ind, ((y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0) (IND_SUC x1).
Definition term6 (x0 : ind -> Prop) := ((x0 IND_0) -> forall y0 : ind, (y0 = IND_0) -> x0 y0) /\ ((forall y0 : ind, (y0 = IND_0) -> x0 y0) -> x0 IND_0).
Definition term5 (x0 : ind -> Prop) := (x0 IND_0) -> forall y0 : ind, (y0 = IND_0) -> x0 y0.
Definition term33 (x0 : ind -> Prop) (x1 : ind) := (forall y0 : ind, ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1) -> (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1.
Definition term11 (x0 : ind) (x1 : ind -> Prop) (x2 : ind) := (x0 = (IND_SUC x2)) /\ (x1 x2).
Definition term51 (x0 : ind -> Prop) := ((forall y0 : ind, (y0 = IND_0) -> x0 y0) /\ (forall y0 : ind, (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0)) -> forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> x0 y0.
Definition term12 (x0 : ind -> Prop) := forall y0 : ind, (x0 y0) -> x0 (IND_SUC y0).
Definition term0 (x0 : ind -> Prop) (x1 : ind) := (x1 = IND_0) -> x0 x1.
Definition term82 (x0 : ind -> Prop) (x1 : ind) := ((fun y0 : ind => (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) x1) -> x0 x1.
Definition term111 (x0 : ind -> Prop) := imp ((x0 IND_0) /\ (forall y0 : ind, (x0 y0) -> x0 (IND_SUC y0))).
Definition term73 (x0 : ind -> Prop) (x1 : ind -> Prop) (x2 : ind) := (fun y0 : ind => ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x1 y1))) x2.
Definition term60 (x0 : ind -> Prop) (x1 : ind) := (x0 x1) -> forall y0 : ind -> Prop, (forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) -> y0 y1) -> y0 x1.
Definition term63 (x0 : ind -> Prop) (x1 : ind -> Prop) := forall y0 : ind, (x0 y0) -> x1 y0.
Definition term76 (x0 : ind -> Prop) (x1 : ind -> Prop) (x2 : ind) := (((x2 = IND_0) \/ (exists y0 : ind, (x2 = (IND_SUC y0)) /\ (x1 y0))) -> x1 x2) -> ((x2 = IND_0) \/ (exists y0 : ind, (x2 = (IND_SUC y0)) /\ (x0 y0))) -> x1 x2.
Definition term97 (x0 : ind -> Prop) := fun y0 : ind => ((fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) y0) -> x0 y0.
Definition term56 (x0 : ind -> Prop) (x1 : ind) := @eq Prop (x0 x1).
Definition term90 (x0 : ind -> Prop) := fun y0 : ind => (x0 y0) -> (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)).
Definition term96 (x0 : ind -> Prop) := forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ ((fun y2 : ind => (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (x0 y3))) y1))) -> (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)).
Definition term72 (x0 : ind -> Prop) (x1 : ind -> Prop) := forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x1 y1)).
Definition term45 (x0 : ind) (x1 : ind -> Prop) := (x0 = IND_0) \/ (exists y0 : ind, (x0 = (IND_SUC y0)) /\ (x1 y0)).
Definition term152 (x0 : ind -> Prop) := (x0 = (fun y0 : ind => forall y1 : ind -> Prop, (forall y2 : ind, ((y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y1 y3))) -> y1 y2) -> y1 y0)) -> ((x0 IND_0) /\ (forall y0 : ind, (x0 y0) -> x0 (IND_SUC y0))) /\ ((forall y0 : ind -> Prop, ((y0 IND_0) /\ (forall y1 : ind, (y0 y1) -> y0 (IND_SUC y1))) -> forall y1 : ind, (x0 y1) -> y0 y1) /\ (forall y0 : ind, (x0 y0) = ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))))).
Definition term20 (x0 : ind -> Prop) (x1 : ind) := forall y0 : ind, (((IND_SUC x1) = (IND_SUC y0)) /\ (x0 y0)) -> x0 (IND_SUC x1).
Definition term149 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) (x3 : ind) := (((x1 = (IND_SUC x3)) -> x1 = (IND_SUC x3)) /\ ((x0 x3) -> x2 x3)) -> ((x1 = (IND_SUC x3)) /\ (x0 x3)) -> (x1 = (IND_SUC x3)) /\ (x2 x3).
Definition term68 (x0 : ind -> Prop) := (fun y0 : ind -> Prop => forall y1 : ind -> Prop, (forall y2 : ind, (y0 y2) -> y1 y2) -> forall y2 : ind, ((y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y0 y3))) -> (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y1 y3))) x0.
Definition term89 (x0 : ind -> Prop) := fun y0 : ind => (x0 y0) -> (fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) y0.
Definition term91 (x0 : ind -> Prop) := forall y0 : ind, (x0 y0) -> (fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) y0.
Definition term1 (x0 : ind -> Prop) := forall y0 : ind, (y0 = IND_0) -> x0 y0.
Definition term106 (x0 : ind -> Prop) := (forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ ((fun y2 : ind => (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (x0 y3))) y1))) -> (fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) y0) -> forall y0 : ind, (x0 y0) -> (fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) y0.
Definition term104 (x0 : ind -> Prop) := (forall y0 : ind, ((fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) y0) -> x0 y0) -> forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ ((fun y2 : ind => (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (x0 y3))) y1))) -> (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)).
Definition term71 (x0 : ind -> Prop) (x1 : ind -> Prop) := (forall y0 : ind, (x0 y0) -> x1 y0) -> forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x1 y1)).
Definition term64 (x0 : ind -> Prop) (x1 : ind -> Prop) := (forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x1 y1))) -> x1 y0) -> forall y0 : ind, (x0 y0) -> x1 y0.
Definition term85 (x0 : ind) (x1 : ind -> Prop) := ((x0 = IND_0) \/ (exists y0 : ind, (x0 = (IND_SUC y0)) /\ ((fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x1 y2))) y0))) -> (x0 = IND_0) \/ (exists y0 : ind, (x0 = (IND_SUC y0)) /\ (x1 y0)).
Definition term74 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := ((x1 = IND_0) \/ (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0))) -> (x1 = IND_0) \/ (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x2 y0)).
Definition term83 (x0 : ind) (x1 : ind -> Prop) := imp ((x0 = IND_0) \/ (exists y0 : ind, (x0 = (IND_SUC y0)) /\ ((fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x1 y2))) y0))).
Definition term81 (x0 : ind) (x1 : ind -> Prop) := imp ((x0 = IND_0) \/ (exists y0 : ind, (x0 = (IND_SUC y0)) /\ (x1 y0))).
Definition term2 (x0 : ind -> Prop) := (fun y0 : ind => (y0 = IND_0) -> x0 y0) IND_0.
Definition term140 (x0 : ind) (x1 : ind -> Prop) := imp (exists y0 : ind, (x0 = (IND_SUC y0)) /\ (x1 y0)).
Definition term93 (x0 : ind -> Prop) := fun y0 : ind => ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ ((fun y2 : ind => (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (x0 y3))) y1))) -> (fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) y0.
Definition term30 (x0 : ind) (x1 : ind -> Prop) := fun y0 : ind => (x0 = (IND_SUC y0)) /\ (x1 y0).
Definition term116 (x0 : ind -> Prop) := (forall y0 : ind -> Prop, ((y0 IND_0) /\ (forall y1 : ind, (y0 y1) -> y0 (IND_SUC y1))) -> forall y1 : ind, (x0 y1) -> y0 y1) /\ (forall y0 : ind, (x0 y0) = ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)))).
Definition term38 (x0 : ind -> Prop) := (forall y0 : ind, (y0 = IND_0) -> x0 y0) /\ (forall y0 : ind, (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0).
Definition term103 (x0 : ind -> Prop) := (fun y0 : ind -> Prop => (forall y1 : ind, ((fun y2 : ind => (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (x0 y3))) y1) -> y0 y1) -> forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ ((fun y3 : ind => (y3 = IND_0) \/ (exists y4 : ind, (y3 = (IND_SUC y4)) /\ (x0 y4))) y2))) -> (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) x0.
Definition term108 (x0 : ind -> Prop) (x1 : ind) := ((x0 x1) -> (x1 = IND_0) \/ (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0))) /\ (((x1 = IND_0) \/ (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0))) -> x0 x1).
Definition term41 (x0 : ind -> Prop) := (x0 IND_0) /\ (forall y0 : ind, (x0 y0) -> x0 (IND_SUC y0)).
Definition term129 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) (x3 : ind) := ((fun y0 : ind => (x1 = (IND_SUC y0)) /\ (x0 y0)) x3) -> (fun y0 : ind => (x1 = (IND_SUC y0)) /\ (x2 y0)) x3.
Definition term113 (x0 : ind -> Prop) := fun y0 : ind -> Prop => (forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) -> y0 y1) -> forall y1 : ind, (x0 y1) -> y0 y1.
Definition term145 (x0 : ind) (x1 : ind) := (fun y0 : Prop => y0 -> y0) (x0 = (IND_SUC x1)).
Definition term119 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 -> x1) /\ (x2 -> x3).
Definition term146 (x0 : ind) (x1 : ind) := (x0 = (IND_SUC x1)) -> x0 = (IND_SUC x1).
Definition term141 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := (exists y0 : ind, (fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x0 y1)) y0) -> exists y0 : ind, (fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x2 y1)) y0.
Definition term3 (x0 : ind -> Prop) := (IND_0 = IND_0) -> x0 IND_0.
Definition term86 (x0 : ind -> Prop) (x1 : ind) := imp (x0 x1).
Definition term144 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := ((x0 -> x2) /\ (x1 -> x3)) -> (x0 /\ x1) -> x2 /\ x3.
Definition term48 (x0 : ind -> Prop) (x1 : ind) := (fun y0 : ind => ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> x0 y0) x1.
Definition term154 := ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) /\ ((forall y0 : ind -> Prop, ((y0 IND_0) /\ (forall y1 : ind, (y0 y1) -> y0 (IND_SUC y1))) -> forall y1 : ind, (NUM_REP y1) -> y0 y1) /\ (forall y0 : ind, (NUM_REP y0) = ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (NUM_REP y1))))).
Definition term147 (x0 : ind -> Prop) (x1 : ind -> Prop) (x2 : ind) := (fun y0 : ind => (x0 y0) -> x1 y0) x2.
Definition term52 (x0 : ind -> Prop) := (((forall y0 : ind, (y0 = IND_0) -> x0 y0) /\ (forall y0 : ind, (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0)) -> forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> x0 y0) /\ ((forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> x0 y0) -> (forall y0 : ind, (y0 = IND_0) -> x0 y0) /\ (forall y0 : ind, (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0)).
Definition term134 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := forall y0 : ind, ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> (x1 = (IND_SUC y0)) /\ (x2 y0).
Definition term46 (x0 : ind -> Prop) (x1 : ind) := ((x1 = IND_0) \/ (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0))) -> x0 x1.
Definition term23 (x0 : ind -> Prop) (x1 : ind) := ((IND_SUC x1) = (IND_SUC x1)) /\ (x0 x1).
Definition term24 (x0 : ind -> Prop) := (forall y0 : ind, forall y1 : ind, ((y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0) -> forall y0 : ind, (x0 y0) -> x0 (IND_SUC y0).
Definition term136 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := imp (forall y0 : ind, ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> (x1 = (IND_SUC y0)) /\ (x2 y0)).
Definition term135 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := imp (forall y0 : ind, ((fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x0 y1)) y0) -> (fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x2 y1)) y0).
Definition term110 (x0 : ind -> Prop) := imp (forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> x0 y0).
Definition term49 (x0 : ind -> Prop) (x1 : ind) := (forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> x0 y0) -> x0 x1.
Definition term28 (x0 : ind -> Prop) (x1 : ind) := (forall y0 : ind, ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1) -> x0 x1.
Definition term150 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := ((x1 = IND_0) -> x1 = IND_0) /\ ((exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0)) -> exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x2 y0)).
Definition term10 (x0 : ind -> Prop) := fun y0 : ind => (y0 = IND_0) -> x0 y0.
Definition term137 (x0 : ind) (x1 : ind -> Prop) := fun y0 : ind => (fun y1 : ind => (x0 = (IND_SUC y1)) /\ (x1 y1)) y0.
Definition term54 (x0 : ind) := (fun y0 : ind => forall y1 : ind -> Prop, (forall y2 : ind, ((y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y1 y3))) -> y1 y2) -> y1 y0) x0.
Definition term17 (x0 : ind -> Prop) (x1 : ind) := forall y0 : ind, ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1.
Definition term4 (x0 : ind -> Prop) := (forall y0 : ind, (y0 = IND_0) -> x0 y0) -> x0 IND_0.
Definition term133 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := forall y0 : ind, ((fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x0 y1)) y0) -> (fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x2 y1)) y0.
Definition term95 (x0 : ind -> Prop) := forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ ((fun y2 : ind => (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (x0 y3))) y1))) -> (fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) y0.
Definition term44 (x0 : ind -> Prop) (x1 : ind) := (fun y0 : ind => (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0) x1.
Definition term29 (x0 : ind) (x1 : ind -> Prop) := exists y0 : ind, (x0 = (IND_SUC y0)) /\ (x1 y0).
Definition term32 (x0 : ind -> Prop) (x1 : ind) := ((exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1) -> forall y0 : ind, ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1.
Definition term75 (x0 : ind -> Prop) (x1 : ind -> Prop) (x2 : ind) := (((x2 = IND_0) \/ (exists y0 : ind, (x2 = (IND_SUC y0)) /\ (x0 y0))) -> (x2 = IND_0) \/ (exists y0 : ind, (x2 = (IND_SUC y0)) /\ (x1 y0))) -> (((x2 = IND_0) \/ (exists y0 : ind, (x2 = (IND_SUC y0)) /\ (x1 y0))) -> x1 x2) -> ((x2 = IND_0) \/ (exists y0 : ind, (x2 = (IND_SUC y0)) /\ (x0 y0))) -> x1 x2.
Definition term39 (x0 : ind -> Prop) := and (x0 IND_0).
Definition term70 (x0 : ind -> Prop) (x1 : ind -> Prop) := (fun y0 : ind -> Prop => (forall y1 : ind, (x0 y1) -> y0 y1) -> forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) -> (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) x1.
Definition term67 (x0 : ind -> Prop) (x1 : ind -> Prop) := (fun y0 : ind -> Prop => (forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) -> y0 y1) -> forall y1 : ind, (x0 y1) -> y0 y1) x1.
Definition term92 (x0 : ind -> Prop) := forall y0 : ind, (x0 y0) -> (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)).
Definition term84 (x0 : ind -> Prop) (x1 : ind) := ((x1 = IND_0) \/ (exists y0 : ind, (x1 = (IND_SUC y0)) /\ ((fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) y0))) -> (fun y0 : ind => (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) x1.
Definition term59 (x0 : ind -> Prop) (x1 : ind) := ((x0 x1) = (forall y0 : ind -> Prop, (forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) -> y0 y1) -> y0 x1)) -> (x0 x1) -> forall y0 : ind -> Prop, (forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) -> y0 y1) -> y0 x1.
Definition term121 (x0 : ind) := (x0 = IND_0) -> x0 = IND_0.
Definition term14 (x0 : ind -> Prop) (x1 : ind) := (x0 x1) -> x0 (IND_SUC x1).
Definition term132 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := fun y0 : ind => ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> (x1 = (IND_SUC y0)) /\ (x2 y0).
Definition term61 (x0 : ind) (x1 : ind -> Prop) := (fun y0 : ind -> Prop => (forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) -> y0 y1) -> y0 x0) x1.
Definition term114 (x0 : ind -> Prop) := fun y0 : ind -> Prop => ((y0 IND_0) /\ (forall y1 : ind, (y0 y1) -> y0 (IND_SUC y1))) -> forall y1 : ind, (x0 y1) -> y0 y1.
Definition term115 (x0 : ind -> Prop) := forall y0 : ind -> Prop, ((y0 IND_0) /\ (forall y1 : ind, (y0 y1) -> y0 (IND_SUC y1))) -> forall y1 : ind, (x0 y1) -> y0 y1.
Definition term37 (x0 : ind -> Prop) := forall y0 : ind, (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0.
Definition term47 (x0 : ind -> Prop) := forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> x0 y0.
Definition term50 (x0 : ind -> Prop) := (forall y0 : ind, ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) -> x0 y0) -> (forall y0 : ind, (y0 = IND_0) -> x0 y0) /\ (forall y0 : ind, (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0).
Definition term40 (x0 : ind -> Prop) := and (forall y0 : ind, (y0 = IND_0) -> x0 y0).
Definition term101 (x0 : ind -> Prop) := fun y0 : ind => (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)).
Definition term42 (x0 : ind -> Prop) (x1 : ind) := (fun y0 : ind => (y0 = IND_0) -> x0 y0) x1.
Definition term31 (x0 : ind -> Prop) (x1 : ind) := (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1.
Definition term99 (x0 : ind -> Prop) := forall y0 : ind, ((fun y1 : ind => (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) y0) -> x0 y0.
Definition term66 := forall y0 : ind -> Prop, forall y1 : ind -> Prop, (forall y2 : ind, (y0 y2) -> y1 y2) -> forall y2 : ind, ((y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y0 y3))) -> (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y1 y3)).
Definition term120 (x0 : ind) := (fun y0 : Prop => y0 -> y0) (x0 = IND_0).
Definition term153 := (NUM_REP = (fun y0 : ind => forall y1 : ind -> Prop, (forall y2 : ind, ((y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y1 y3))) -> y1 y2) -> y1 y0)) -> ((NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0))) /\ ((forall y0 : ind -> Prop, ((y0 IND_0) /\ (forall y1 : ind, (y0 y1) -> y0 (IND_SUC y1))) -> forall y1 : ind, (NUM_REP y1) -> y0 y1) /\ (forall y0 : ind, (NUM_REP y0) = ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (NUM_REP y1))))).
Definition term128 (x0 : ind) (x1 : ind -> Prop) (x2 : ind) := imp ((x0 = (IND_SUC x2)) /\ (x1 x2)).
Definition term62 (x0 : ind -> Prop) (x1 : ind -> Prop) (x2 : ind) := (x0 x2) -> x1 x2.
Definition term142 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0)) -> exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x2 y0).
Definition term25 (x0 : ind -> Prop) := (forall y0 : ind, (x0 y0) -> x0 (IND_SUC y0)) -> forall y0 : ind, forall y1 : ind, ((y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0.
Definition term131 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := fun y0 : ind => ((fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x0 y1)) y0) -> (fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x2 y1)) y0.
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term151 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := (((x1 = IND_0) -> x1 = IND_0) /\ ((exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0)) -> exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x2 y0))) -> ((x1 = IND_0) \/ (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0))) -> (x1 = IND_0) \/ (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x2 y0)).
Definition term100 (x0 : ind -> Prop) := (fun y0 : ind -> Prop => forall y1 : ind -> Prop, (forall y2 : ind, (y0 y2) -> y1 y2) -> forall y2 : ind, ((y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y0 y3))) -> (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y1 y3))) (fun y0 : ind => (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))).
Definition term18 (x0 : ind -> Prop) := forall y0 : ind, forall y1 : ind, ((y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0.
Definition term117 (x0 : ind -> Prop) := ((x0 IND_0) /\ (forall y0 : ind, (x0 y0) -> x0 (IND_SUC y0))) /\ ((forall y0 : ind -> Prop, ((y0 IND_0) /\ (forall y1 : ind, (y0 y1) -> y0 (IND_SUC y1))) -> forall y1 : ind, (x0 y1) -> y0 y1) /\ (forall y0 : ind, (x0 y0) = ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))))).
Definition term139 (x0 : ind) (x1 : ind -> Prop) := imp (exists y0 : ind, (fun y1 : ind => (x0 = (IND_SUC y1)) /\ (x1 y1)) y0).
Definition term148 (x0 : ind) (x1 : ind -> Prop) (x2 : ind -> Prop) (x3 : ind) := ((x0 = (IND_SUC x3)) -> x0 = (IND_SUC x3)) /\ ((x1 x3) -> x2 x3).
Definition term13 (x0 : ind -> Prop) (x1 : ind) := (fun y0 : ind => (x0 y0) -> x0 (IND_SUC y0)) x1.
Definition term78 (x0 : ind -> Prop) (x1 : ind) := (fun y0 : ind => (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) x1.
Definition term21 (x0 : ind -> Prop) (x1 : ind) := (fun y0 : ind => (((IND_SUC x1) = (IND_SUC y0)) /\ (x0 y0)) -> x0 (IND_SUC x1)) x1.
Definition term55 (x0 : ind) := forall y0 : ind -> Prop, (forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) -> y0 y1) -> y0 x0.
Definition term94 (x0 : ind -> Prop) := fun y0 : ind => ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ ((fun y2 : ind => (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (x0 y3))) y1))) -> (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)).
Definition term126 (x0 : ind) (x1 : ind -> Prop) (x2 : ind) := (fun y0 : ind => (x0 = (IND_SUC y0)) /\ (x1 y0)) x2.
Definition term102 (x0 : ind -> Prop) := forall y0 : ind -> Prop, (forall y1 : ind, ((fun y2 : ind => (y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (x0 y3))) y1) -> y0 y1) -> forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ ((fun y3 : ind => (y3 = IND_0) \/ (exists y4 : ind, (y3 = (IND_SUC y4)) /\ (x0 y4))) y2))) -> (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2)).
Definition term69 (x0 : ind -> Prop) := forall y0 : ind -> Prop, (forall y1 : ind, (x0 y1) -> y0 y1) -> forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (x0 y2))) -> (y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2)).
Definition term65 (x0 : ind -> Prop) := forall y0 : ind -> Prop, (forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) -> y0 y1) -> forall y1 : ind, (x0 y1) -> y0 y1.
Definition term79 (x0 : ind -> Prop) (x1 : ind) := @eq Prop ((fun y0 : ind => (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) x1).
Definition term88 (x0 : ind) (x1 : ind -> Prop) := (x1 x0) -> (x0 = IND_0) \/ (exists y0 : ind, (x0 = (IND_SUC y0)) /\ (x1 y0)).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x1 y0.
Definition term7 (x0 : ind -> Prop) (x1 : ind) := ((x1 = IND_0) -> x0 x1) -> x0 x1.
Definition term109 (x0 : ind -> Prop) := forall y0 : ind, (x0 y0) = ((y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))).
Definition term107 (x0 : ind -> Prop) (x1 : ind) := (fun y0 : ind => (x0 y0) -> (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) x1.
Definition term118 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := ((x0 -> x2) /\ (x1 -> x3)) -> (x0 \/ x1) -> x2 \/ x3.
Definition term8 (x0 : ind -> Prop) (x1 : ind) := ((x1 = IND_0) -> x0 x1) -> (x1 = IND_0) -> x0 x1.
Definition term87 (x0 : ind -> Prop) (x1 : ind) := (x0 x1) -> (fun y0 : ind => (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))) x1.
Definition term34 (x0 : ind -> Prop) (x1 : ind) := ((forall y0 : ind, ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1) -> (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1) /\ (((exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1) -> forall y0 : ind, ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1).
Definition term27 (x0 : ind -> Prop) (x1 : ind) (x2 : ind) := (fun y0 : ind => ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> x0 x1) x2.
Definition term26 (x0 : ind -> Prop) := ((forall y0 : ind, (x0 y0) -> x0 (IND_SUC y0)) -> forall y0 : ind, forall y1 : ind, ((y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0) /\ ((forall y0 : ind, forall y1 : ind, ((y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0) -> forall y0 : ind, (x0 y0) -> x0 (IND_SUC y0)).
Definition term57 (x0 : ind -> Prop) := forall y0 : ind, (x0 y0) = (forall y1 : ind -> Prop, (forall y2 : ind, ((y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y1 y3))) -> y1 y2) -> y1 y0).
Definition term112 (x0 : ind -> Prop) (x1 : ind -> Prop) := ((x1 IND_0) /\ (forall y0 : ind, (x1 y0) -> x1 (IND_SUC y0))) -> forall y0 : ind, (x0 y0) -> x1 y0.
Definition term36 (x0 : ind -> Prop) := fun y0 : ind => (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0.
Definition term130 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) (x3 : ind) := ((x1 = (IND_SUC x3)) /\ (x0 x3)) -> (x1 = (IND_SUC x3)) /\ (x2 x3).
Definition term143 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := (forall y0 : ind, ((x1 = (IND_SUC y0)) /\ (x0 y0)) -> (x1 = (IND_SUC y0)) /\ (x2 y0)) -> (exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x0 y0)) -> exists y0 : ind, (x1 = (IND_SUC y0)) /\ (x2 y0).
Definition term125 (x0 : ind -> Prop) (x1 : ind) (x2 : ind -> Prop) := (forall y0 : ind, ((fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x0 y1)) y0) -> (fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x2 y1)) y0) -> (exists y0 : ind, (fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x0 y1)) y0) -> exists y0 : ind, (fun y1 : ind => (x1 = (IND_SUC y1)) /\ (x2 y1)) y0.
Definition term124 (x0 : ind -> Prop) (x1 : ind -> Prop) := (forall y0 : ind, (x0 y0) -> x1 y0) -> (exists y0 : ind, x0 y0) -> exists y0 : ind, x1 y0.
Definition term77 (x0 : ind -> Prop) (x1 : ind -> Prop) (x2 : ind) := ((x2 = IND_0) \/ (exists y0 : ind, (x2 = (IND_SUC y0)) /\ (x0 y0))) -> x1 x2.
Definition term53 := fun y0 : ind => forall y1 : ind -> Prop, (forall y2 : ind, ((y2 = IND_0) \/ (exists y3 : ind, (y2 = (IND_SUC y3)) /\ (y1 y3))) -> y1 y2) -> y1 y0.
Definition term35 (x0 : ind -> Prop) := fun y0 : ind => forall y1 : ind, ((y0 = (IND_SUC y1)) /\ (x0 y1)) -> x0 y0.
Definition term105 (x0 : ind -> Prop) := (fun y0 : ind -> Prop => (forall y1 : ind, ((y1 = IND_0) \/ (exists y2 : ind, (y1 = (IND_SUC y2)) /\ (y0 y2))) -> y0 y1) -> forall y1 : ind, (x0 y1) -> y0 y1) (fun y0 : ind => (y0 = IND_0) \/ (exists y1 : ind, (y0 = (IND_SUC y1)) /\ (x0 y1))).
Definition term22 (x0 : ind -> Prop) (x1 : ind) := (((IND_SUC x1) = (IND_SUC x1)) /\ (x0 x1)) -> x0 (IND_SUC x1).
