Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (forall y0 : a0, (x0 y0) = (x1 = y0)).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, (x0 y0) -> y0 = x1) /\ (forall y0 : a0, (y0 = x1) -> x0 x1).
Definition term69 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (forall y0 : a0, (x1 y0) -> y0 = x0) /\ (forall y0 : a0, (y0 = x0) -> x1 y0).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((forall y0 : a0, (x0 y0) -> y0 = x1) /\ (forall y0 : a0, (y0 = x1) -> x0 x1)).
Definition term70 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (x1 y0) -> y0 = x0) /\ (forall y0 : a0, (y0 = x0) -> x1 y0)).
Definition term13 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((forall y0 : a0, (x0 y0) -> y0 = x1) /\ (x0 x1)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (y0 = x1) -> x0 x1.
Definition term24 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> (x0 -> x1) /\ (x1 -> x0)) /\ (((x0 -> x1) /\ (x1 -> x0)) -> x0 = x1).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and ((fun y0 : a0 => (x0 y0) -> y0 = x1) x2).
Definition term50 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, ((x1 y0) -> y0 = x0) /\ ((y0 = x0) -> x1 y0)).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, ((x1 y0) -> x0 = y0) /\ ((x0 = y0) -> x1 y0)).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (forall y0 : a0, (fun y1 : a0 => (x0 y1) -> y1 = x1) y0).
Definition term59 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => (x1 y1) -> y1 = x0) y0) /\ ((fun y1 : a0 => (y1 = x0) -> x1 y1) y0).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((x0 x1) /\ (forall y0 : a0, (x0 y0) -> y0 = x1)).
Definition term67 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (fun y1 : a0 => (y1 = x0) -> x1 y1) y0.
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (fun y1 : a0 => (x0 y1) -> y1 = x1) y0.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and ((x0 x2) -> x1 = x2).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := ((x1 = x2) = (x1 = x2)) -> ((x1 = x2) -> (x0 x1) = x3) -> ((x1 = x2) -> x0 x1) = ((x1 = x2) -> x3).
Definition term68 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (y0 = x0) -> x1 y0.
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y1 = y0) x0.
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := ((x1 = x2) -> (x0 x1) = x3) -> ((x1 = x2) -> x0 x1) = ((x1 = x2) -> x3).
Definition term107 (a0 : Type') := forall y0 : a0 -> Prop, (@ex1 a0 (fun y1 : a0 => y0 y1)) = (exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (y0 y2) -> y2 = y1)).
Definition term12 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0)) x0.
Definition term21 (x0 : Prop) (x1 : Prop) := (x1 -> x0) /\ (x0 -> x1).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (exists y0 : a0, y0 = x1) -> x0 x1.
Definition term75 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x2 = x0) = y0) -> (y0 -> (x1 x2) = y1) -> ((x2 = x0) -> x1 x2) = (y0 -> y1)) x3.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term92 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((fun y0 : a0 => y0 = x2) x0) -> x1 x2.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => (forall y1 : a0, (x0 y1) -> y0) = ((exists y1 : a0, x0 y1) -> y0)) x1.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, (x0 y1) /\ (y0 y1)) = ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)).
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, ((fun y1 : a0 => (x1 y1) -> y1 = x0) y0) /\ ((fun y1 : a0 => (y1 = x0) -> x1 y1) y0).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x2) -> x1 = x2.
Definition term15 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 -> x1.
Definition term58 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((fun y0 : a0 => (x1 y0) -> y0 = x0) x2) /\ ((fun y0 : a0 => (y0 = x0) -> x1 y0) x2).
Definition term71 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, forall y1 : a0, (x0 y1) = (y0 = y1).
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) (x4 : Prop) := ((x2 = x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((x2 = x0) -> x1 x2) = (x3 -> x4).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0, (x0 y1) = (y0 = y1).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) -> x1 = x2.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (x0 y0) = (x1 = y0).
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, ((x1 y0) -> y0 = x0) /\ ((y0 = x0) -> x1 y0).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, ((x1 y0) -> x0 = y0) /\ ((x0 = y0) -> x1 y0).
Definition term99 (a0 : Type') (x0 : a0) := imp (exists y0 : a0, y0 = x0).
Definition term97 (a0 : Type') (x0 : a0) := exists y0 : a0, (fun y1 : a0 => y1 = x0) y0.
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, (x0 y0) -> y0 = x1) /\ (x0 x1).
Definition term16 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 -> x1.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, ((fun y1 : a0 => y1 = x1) y0) -> x0 x1.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and ((x0 x1) -> x1 = x2).
Definition term96 (a0 : Type') (x0 : a0) := fun y0 : a0 => (fun y1 : a0 => y1 = x0) y0.
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (x0 y0) -> y0 = x1.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (forall y2 : a0, (y0 y2) /\ (y1 y2)) = ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2))) x0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, (forall y2 : a0, (y0 y2) -> y1) = ((exists y2 : a0, y0 y2) -> y1)) x0.
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (x0 = y0) = (y0 = x0)) x1.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) /\ (forall y0 : a0, (x0 y0) -> y0 = x1).
Definition term98 (a0 : Type') (x0 : a0) := imp (exists y0 : a0, (fun y1 : a0 => y1 = x0) y0).
Definition term22 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> (x1 -> x0) /\ (x0 -> x1).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (exists y0 : a0, forall y1 : a0, (x0 y1) = (y0 = y1)).
Definition term76 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := forall y0 : Prop, ((x2 = x0) = x3) -> (x3 -> (x1 x2) = y0) -> ((x2 = x0) -> x1 x2) = (x3 -> y0).
Definition term72 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term1 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term91 (a0 : Type') (x0 : a0) (x1 : a0) := imp ((fun y0 : a0 => y0 = x0) x1).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (x0 y0) -> y0 = x1.
Definition term74 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, ((x2 = x0) = y0) -> (y0 -> (x1 x2) = y1) -> ((x2 = x0) -> x1 x2) = (y0 -> y1).
Definition term73 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term89 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) -> x1 x2.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (x0 y0) /\ (forall y1 : a0, (x0 y1) -> y1 = y0).
Definition term77 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((x2 = x0) = x3) -> (x3 -> (x1 x2) = y0) -> ((x2 = x0) -> x1 x2) = (x3 -> y0)) x4.
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0) := imp (x0 = x1).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 = x2) -> x1 x2.
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (x0 y0) -> y0 = x1) x2.
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (forall y0 : a0, (x0 y0) -> y0 = x1).
Definition term82 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x0 = x2) -> (x1 x0) = (x1 x2)) -> ((x0 = x2) -> x1 x0) = ((x0 = x2) -> x1 x2).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := @ex1 a0 (fun y0 : a0 => x0 y0).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((x1 y0) -> x0 = y0) /\ ((x0 = y0) -> x1 y0).
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (y0 = x0) -> x1 y0.
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (@ex1 a0 (fun y0 : a0 => x0 y0)).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (exists y0 : a0, (fun y1 : a0 => y1 = x1) y0) -> x0 x1.
Definition term106 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (x0 y0) /\ (forall y1 : a0, (x0 y1) -> y1 = y0).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((fun y1 : a0 => y1 = x1) y0) -> x0 x1.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, (forall y1 : a0, (x0 y1) -> y0) = ((exists y1 : a0, x0 y1) -> y0).
Definition term18 (x0 : Prop) (x1 : Prop) := (x1 -> x0) -> (x0 -> x1) -> x1.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := True -> x0 x1.
Definition term17 (x0 : Prop) (x1 : Prop) := (x0 -> x1) -> x1.
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (x0 y0) = (x1 = y0).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (y0 = x1) -> x0 x1.
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 = x2) -> (x1 x0) = (x1 x2).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (fun y1 : a0 => (x0 y1) -> y1 = x1) y0.
Definition term19 (x0 : Prop) (x1 : Prop) := (x1 -> x0) -> x1.
Definition term66 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (y1 = x0) -> x1 y1) y0.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@ex1 a0 (fun y1 : a0 => y0 y1)) = (exists y1 : a0, forall y2 : a0, (y0 y2) = (y1 = y2))) x0.
Definition term20 (x0 : Prop) (x1 : Prop) := (x0 -> x1) -> (x1 -> x0) -> x1.
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (forall y0 : a0, (fun y1 : a0 => (x1 y1) -> y1 = x0) y0) /\ (forall y0 : a0, (fun y1 : a0 => (y1 = x0) -> x1 y1) y0).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) -> x2 = x0) /\ ((x2 = x0) -> x1 x2).
Definition term60 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, ((fun y1 : a0 => (x1 y1) -> y1 = x0) y0) /\ ((fun y1 : a0 => (y1 = x0) -> x1 y1) y0)).
Definition term57 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (y0 = x0) -> x1 y0) x2.
Definition term90 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => y0 = x0) x1.
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (forall y0 : a0, (y0 = x1) -> x0 x1).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (forall y0 : a0, ((fun y1 : a0 => y1 = x1) y0) -> x0 x1).
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((x1 y0) -> y0 = x0) /\ ((y0 = x0) -> x1 y0).
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) -> x0 = x2) /\ ((x0 = x2) -> x1 x2).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (x0 y1) /\ (y0 y1)) = ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1))) x1.
Definition term23 (x0 : Prop) (x1 : Prop) := ((x0 -> x1) /\ (x1 -> x0)) -> x0 = x1.
