Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) (x2 : recspace a0) (x3 : a0) := (fun y0 : a0 => (x2 = (x0 y0)) -> x1 x2) x3.
Definition term37 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) := and (forall y0 : recspace a0, (y0 = x0) -> x1 y0).
Definition term101 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : recspace a0) := ((x2 x3) -> (x3 = x0) \/ (exists y0 : a0, x3 = (x1 y0))) /\ (((x3 = x0) \/ (exists y0 : a0, x3 = (x1 y0))) -> x2 x3).
Definition term19 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := (fun y0 : a0 => ((x1 x2) = (x1 y0)) -> x0 (x1 x2)) x2.
Definition term93 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := (fun y0 : type1338 a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, (y0 y2) -> y1 y2) -> forall y2 : recspace a0, ((y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) -> (y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) (fun y0 : recspace a0 => (y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))).
Definition term16 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) := forall y0 : recspace a0, forall y1 : a0, (y0 = (x0 y1)) -> x1 y0.
Definition term72 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : recspace a0) := (((x3 = x0) \/ (exists y0 : a0, x3 = (x1 y0))) -> (x3 = x0) \/ (exists y0 : a0, x3 = (x1 y0))) -> (((x3 = x0) \/ (exists y0 : a0, x3 = (x1 y0))) -> x2 x3) -> ((x3 = x0) \/ (exists y0 : a0, x3 = (x1 y0))) -> x2 x3.
Definition term73 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : recspace a0) := (((x3 = x0) \/ (exists y0 : a0, x3 = (x1 y0))) -> x2 x3) -> ((x3 = x0) \/ (exists y0 : a0, x3 = (x1 y0))) -> x2 x3.
Definition term76 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : recspace a0) := imp ((fun y0 : recspace a0 => (y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) x2).
Definition term52 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : recspace a0) := forall y0 : type1338 a0, (forall y1 : recspace a0, ((y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) -> y0 y1) -> y0 x2.
Definition term43 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : recspace a0) := ((x3 = x0) \/ (exists y0 : a0, x3 = (x1 y0))) -> x2 x3.
Definition term78 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : recspace a0) := ((fun y0 : recspace a0 => (y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) x3) -> x2 x3.
Definition term35 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := (forall y0 : recspace a0, (y0 = x0) -> x2 y0) /\ (forall y0 : recspace a0, (exists y1 : a0, y0 = (x1 y1)) -> x2 y0).
Definition term75 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : recspace a0) := @eq Prop ((fun y0 : recspace a0 => (y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) x2).
Definition term56 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) (x3 : recspace a0) := ((x0 x3) = (forall y0 : type1338 a0, (forall y1 : recspace a0, ((y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) -> y0 y1) -> y0 x3)) -> (x0 x3) -> forall y0 : type1338 a0, (forall y1 : recspace a0, ((y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) -> y0 y1) -> y0 x3.
Definition term61 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : type1338 a0) := (forall y0 : recspace a0, ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> x3 y0) -> forall y0 : recspace a0, (x2 y0) -> x3 y0.
Definition term3 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := (x1 = x1) -> x0 x1.
Definition term85 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := forall y0 : recspace a0, (x0 y0) -> (fun y1 : recspace a0 => (y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) y0.
Definition term7 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) (x2 : recspace a0) := ((x2 = x0) -> x1 x2) -> x1 x2.
Definition term58 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : recspace a0) (x3 : type1338 a0) := (fun y0 : type1338 a0 => (forall y1 : recspace a0, ((y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) -> y0 y1) -> y0 x2) x3.
Definition term33 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) := fun y0 : recspace a0 => (exists y1 : a0, y0 = (x0 y1)) -> x1 y0.
Definition term70 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : recspace a0) := (fun y0 : recspace a0 => ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> (y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) x2.
Definition term30 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) (x2 : recspace a0) := (forall y0 : a0, (x2 = (x0 y0)) -> x1 x2) -> (exists y0 : a0, x2 = (x0 y0)) -> x1 x2.
Definition term84 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := fun y0 : recspace a0 => (x0 y0) -> (y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1)).
Definition term77 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) (x2 : type1432 a0) := imp ((x1 = x0) \/ (exists y0 : a0, x1 = (x2 y0))).
Definition term69 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := forall y0 : recspace a0, ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> (y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1)).
Definition term65 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := (fun y0 : type1338 a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, (y0 y2) -> y1 y2) -> forall y2 : recspace a0, ((y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) -> (y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) x2.
Definition term11 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) := forall y0 : a0, x0 (x1 y0).
Definition term34 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) := forall y0 : recspace a0, (exists y1 : a0, y0 = (x0 y1)) -> x1 y0.
Definition term38 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) (x2 : type1432 a0) := (x1 x0) /\ (forall y0 : a0, x1 (x2 y0)).
Definition term48 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := ((forall y0 : recspace a0, (y0 = x0) -> x2 y0) /\ (forall y0 : recspace a0, (exists y1 : a0, y0 = (x1 y1)) -> x2 y0)) -> forall y0 : recspace a0, ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> x2 y0.
Definition term82 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : recspace a0) (x3 : type1432 a0) := (x0 x2) -> (x2 = x1) \/ (exists y0 : a0, x2 = (x3 y0)).
Definition term111 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) (x2 : type1432 a0) := (fun y0 : Prop => y0 -> y0) ((x1 = x0) \/ (exists y0 : a0, x1 = (x2 y0))).
Definition term14 (a0 : Type') (x0 : type1432 a0) (x1 : a0) (x2 : type1338 a0) (x3 : recspace a0) := (x3 = (x0 x1)) -> x2 x3.
Definition term104 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) (x2 : type1432 a0) := imp ((x1 x0) /\ (forall y0 : a0, x1 (x2 y0))).
Definition term8 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) (x2 : recspace a0) := ((x2 = x0) -> x1 x2) -> (x2 = x0) -> x1 x2.
Definition term88 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := fun y0 : recspace a0 => ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> (y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1)).
Definition term89 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := forall y0 : recspace a0, ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> (fun y1 : recspace a0 => (y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) y0.
Definition term71 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) (x2 : type1432 a0) := ((x1 = x0) \/ (exists y0 : a0, x1 = (x2 y0))) -> (x1 = x0) \/ (exists y0 : a0, x1 = (x2 y0)).
Definition term12 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := (fun y0 : a0 => x0 (x1 y0)) x2.
Definition term1 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) := forall y0 : recspace a0, (y0 = x0) -> x1 y0.
Definition term49 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := (((forall y0 : recspace a0, (y0 = x0) -> x2 y0) /\ (forall y0 : recspace a0, (exists y1 : a0, y0 = (x1 y1)) -> x2 y0)) -> forall y0 : recspace a0, ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> x2 y0) /\ ((forall y0 : recspace a0, ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> x2 y0) -> (forall y0 : recspace a0, (y0 = x0) -> x2 y0) /\ (forall y0 : recspace a0, (exists y1 : a0, y0 = (x1 y1)) -> x2 y0)).
Definition term53 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := @eq Prop (x0 x1).
Definition term6 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := ((x0 x1) -> forall y0 : recspace a0, (y0 = x1) -> x0 y0) /\ ((forall y0 : recspace a0, (y0 = x1) -> x0 y0) -> x0 x1).
Definition term9 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) (x2 : recspace a0) := (((x2 = x0) -> x1 x2) -> (x2 = x0) -> x1 x2) /\ (((x2 = x0) -> x1 x2) -> (x2 = x0) -> x1 x2).
Definition term90 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := fun y0 : recspace a0 => ((fun y1 : recspace a0 => (y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) y0) -> x2 y0.
Definition term29 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) (x2 : recspace a0) := ((exists y0 : a0, x2 = (x0 y0)) -> x1 x2) -> forall y0 : a0, (x2 = (x0 y0)) -> x1 x2.
Definition term25 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) (x2 : recspace a0) := (forall y0 : a0, (x2 = (x0 y0)) -> x1 x2) -> x1 x2.
Definition term102 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := forall y0 : recspace a0, (x0 y0) = ((y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1))).
Definition term103 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := imp (forall y0 : recspace a0, ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> x2 y0).
Definition term87 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := fun y0 : recspace a0 => ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> (fun y1 : recspace a0 => (y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) y0.
Definition term92 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := forall y0 : recspace a0, ((fun y1 : recspace a0 => (y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) y0) -> x2 y0.
Definition term5 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) := (x1 x0) -> forall y0 : recspace a0, (y0 = x0) -> x1 y0.
Definition term106 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := fun y0 : type1338 a0 => (forall y1 : recspace a0, ((y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) -> y0 y1) -> forall y1 : recspace a0, (x2 y1) -> y0 y1.
Definition term44 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := forall y0 : recspace a0, ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> x2 y0.
Definition term59 (a0 : Type') (x0 : type1338 a0) (x1 : type1338 a0) (x2 : recspace a0) := (x0 x2) -> x1 x2.
Definition term107 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := fun y0 : type1338 a0 => ((y0 x0) /\ (forall y1 : a0, y0 (x1 y1))) -> forall y1 : recspace a0, (x2 y1) -> y0 y1.
Definition term18 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := forall y0 : a0, ((x1 x2) = (x1 y0)) -> x0 (x1 x2).
Definition term54 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := forall y0 : recspace a0, (x0 y0) = (forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x1) \/ (exists y3 : a0, y2 = (x2 y3))) -> y1 y2) -> y1 y0).
Definition term21 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) := (forall y0 : recspace a0, forall y1 : a0, (y0 = (x1 y1)) -> x0 y0) -> forall y0 : a0, x0 (x1 y0).
Definition term96 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := (fun y0 : type1338 a0 => (forall y1 : recspace a0, ((fun y2 : recspace a0 => (y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) y1) -> y0 y1) -> forall y1 : recspace a0, ((y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) -> (y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) x2.
Definition term80 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := imp (x0 x1).
Definition term4 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := (forall y0 : recspace a0, (y0 = x1) -> x0 y0) -> x0 x1.
Definition term57 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) (x3 : recspace a0) := (x0 x3) -> forall y0 : type1338 a0, (forall y1 : recspace a0, ((y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) -> y0 y1) -> y0 x3.
Definition term42 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) (x2 : type1432 a0) := (x1 = x0) \/ (exists y0 : a0, x1 = (x2 y0)).
Definition term32 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) := fun y0 : recspace a0 => forall y1 : a0, (y0 = (x0 y1)) -> x1 y0.
Definition term22 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) := (forall y0 : a0, x1 (x0 y0)) -> forall y0 : recspace a0, forall y1 : a0, (y0 = (x0 y1)) -> x1 y0.
Definition term15 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) (x2 : recspace a0) := forall y0 : a0, (x2 = (x0 y0)) -> x1 x2.
Definition term17 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := (fun y0 : recspace a0 => forall y1 : a0, (y0 = (x1 y1)) -> x0 y0) (x1 x2).
Definition term13 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := x0 (x1 x2).
Definition term108 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := forall y0 : type1338 a0, ((y0 x0) /\ (forall y1 : a0, y0 (x1 y1))) -> forall y1 : recspace a0, (x2 y1) -> y0 y1.
Definition term109 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := (forall y0 : type1338 a0, ((y0 x1) /\ (forall y1 : a0, y0 (x2 y1))) -> forall y1 : recspace a0, (x0 y1) -> y0 y1) /\ (forall y0 : recspace a0, (x0 y0) = ((y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1)))).
Definition term47 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := (forall y0 : recspace a0, ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> x2 y0) -> (forall y0 : recspace a0, (y0 = x0) -> x2 y0) /\ (forall y0 : recspace a0, (exists y1 : a0, y0 = (x1 y1)) -> x2 y0).
Definition term81 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) (x3 : recspace a0) := (x0 x3) -> (fun y0 : recspace a0 => (y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1))) x3.
Definition term51 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : recspace a0) := (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) -> y1 y2) -> y1 y0) x2.
Definition term36 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := and (x0 x1).
Definition term63 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := forall y0 : type1338 a0, forall y1 : type1338 a0, (forall y2 : recspace a0, (y0 y2) -> y1 y2) -> forall y2 : recspace a0, ((y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) -> (y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3)).
Definition term83 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := fun y0 : recspace a0 => (x0 y0) -> (fun y1 : recspace a0 => (y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) y0.
Definition term28 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) (x2 : recspace a0) := (exists y0 : a0, x2 = (x0 y0)) -> x1 x2.
Definition term98 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := (fun y0 : type1338 a0 => (forall y1 : recspace a0, ((y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) -> y0 y1) -> forall y1 : recspace a0, (x0 y1) -> y0 y1) (fun y0 : recspace a0 => (y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1))).
Definition term27 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := fun y0 : a0 => x0 = (x1 y0).
Definition term46 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : recspace a0) := (forall y0 : recspace a0, ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> x2 y0) -> x2 x3.
Definition term26 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := exists y0 : a0, x0 = (x1 y0).
Definition term99 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := (forall y0 : recspace a0, ((y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1))) -> (fun y1 : recspace a0 => (y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) y0) -> forall y0 : recspace a0, (x0 y0) -> (fun y1 : recspace a0 => (y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) y0.
Definition term50 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) -> y1 y2) -> y1 y0.
Definition term91 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := fun y0 : recspace a0 => ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> x2 y0.
Definition term55 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) (x3 : recspace a0) := (fun y0 : recspace a0 => (x0 y0) = (forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x1) \/ (exists y3 : a0, y2 = (x2 y3))) -> y1 y2) -> y1 y0)) x3.
Definition term95 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := forall y0 : type1338 a0, (forall y1 : recspace a0, ((fun y2 : recspace a0 => (y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) y1) -> y0 y1) -> forall y1 : recspace a0, ((y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) -> (y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2)).
Definition term66 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := forall y0 : type1338 a0, (forall y1 : recspace a0, (x0 y1) -> y0 y1) -> forall y1 : recspace a0, ((y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) -> (y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2)).
Definition term62 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) := forall y0 : type1338 a0, (forall y1 : recspace a0, ((y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) -> y0 y1) -> forall y1 : recspace a0, (x2 y1) -> y0 y1.
Definition term0 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) (x2 : recspace a0) := (x2 = x0) -> x1 x2.
Definition term39 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) (x2 : recspace a0) := (fun y0 : recspace a0 => (y0 = x0) -> x1 y0) x2.
Definition term2 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := (fun y0 : recspace a0 => (y0 = x1) -> x0 y0) x1.
Definition term94 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := fun y0 : recspace a0 => (y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1)).
Definition term97 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := (forall y0 : recspace a0, ((fun y1 : recspace a0 => (y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) y0) -> x0 y0) -> forall y0 : recspace a0, ((y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1))) -> (y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1)).
Definition term68 (a0 : Type') (x0 : type1338 a0) (x1 : type1338 a0) (x2 : recspace a0) (x3 : type1432 a0) := (forall y0 : recspace a0, (x0 y0) -> x1 y0) -> forall y0 : recspace a0, ((y0 = x2) \/ (exists y1 : a0, y0 = (x3 y1))) -> (y0 = x2) \/ (exists y1 : a0, y0 = (x3 y1)).
Definition term10 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) := fun y0 : recspace a0 => (y0 = x0) -> x1 y0.
Definition term100 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) (x3 : recspace a0) := (fun y0 : recspace a0 => (x0 y0) -> (y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1))) x3.
Definition term86 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := forall y0 : recspace a0, (x0 y0) -> (y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1)).
Definition term105 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : type1338 a0) := ((x3 x0) /\ (forall y0 : a0, x3 (x1 y0))) -> forall y0 : recspace a0, (x2 y0) -> x3 y0.
Definition term23 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) := ((forall y0 : a0, x0 (x1 y0)) -> forall y0 : recspace a0, forall y1 : a0, (y0 = (x1 y1)) -> x0 y0) /\ ((forall y0 : recspace a0, forall y1 : a0, (y0 = (x1 y1)) -> x0 y0) -> forall y0 : a0, x0 (x1 y0)).
Definition term41 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) (x2 : recspace a0) := (fun y0 : recspace a0 => (exists y1 : a0, y0 = (x0 y1)) -> x1 y0) x2.
Definition term40 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : recspace a0) := ((forall y0 : recspace a0, (y0 = x0) -> x2 y0) /\ (forall y0 : recspace a0, (exists y1 : a0, y0 = (x1 y1)) -> x2 y0)) -> x2 x3.
Definition term74 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : recspace a0) := (fun y0 : recspace a0 => (y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) x2.
Definition term20 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := ((x1 x2) = (x1 x2)) -> x0 (x1 x2).
Definition term60 (a0 : Type') (x0 : type1338 a0) (x1 : type1338 a0) := forall y0 : recspace a0, (x0 y0) -> x1 y0.
Definition term67 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) (x3 : type1338 a0) := (fun y0 : type1338 a0 => (forall y1 : recspace a0, (x0 y1) -> y0 y1) -> forall y1 : recspace a0, ((y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) -> (y1 = x1) \/ (exists y2 : a0, y1 = (x2 y2))) x3.
Definition term64 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : type1338 a0) := (fun y0 : type1338 a0 => (forall y1 : recspace a0, ((y1 = x0) \/ (exists y2 : a0, y1 = (x1 y2))) -> y0 y1) -> forall y1 : recspace a0, (x2 y1) -> y0 y1) x3.
Definition term31 (a0 : Type') (x0 : type1432 a0) (x1 : type1338 a0) (x2 : recspace a0) := ((forall y0 : a0, (x2 = (x0 y0)) -> x1 x2) -> (exists y0 : a0, x2 = (x0 y0)) -> x1 x2) /\ (((exists y0 : a0, x2 = (x0 y0)) -> x1 x2) -> forall y0 : a0, (x2 = (x0 y0)) -> x1 x2).
Definition term110 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := ((x0 x1) /\ (forall y0 : a0, x0 (x2 y0))) /\ ((forall y0 : type1338 a0, ((y0 x1) /\ (forall y1 : a0, y0 (x2 y1))) -> forall y1 : recspace a0, (x0 y1) -> y0 y1) /\ (forall y0 : recspace a0, (x0 y0) = ((y0 = x1) \/ (exists y1 : a0, y0 = (x2 y1))))).
Definition term79 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : recspace a0) := ((x2 = x0) \/ (exists y0 : a0, x2 = (x1 y0))) -> (fun y0 : recspace a0 => (y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) x2.
Definition term45 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : recspace a0) := (fun y0 : recspace a0 => ((y0 = x0) \/ (exists y1 : a0, y0 = (x1 y1))) -> x2 y0) x3.