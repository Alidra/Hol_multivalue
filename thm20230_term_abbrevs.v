Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) := (x3 = x0) -> x1 = (x2 x3).
Definition term55 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := (True -> (x0 = (x1 x2)) = x3) -> ((exists y0 : a0, y0 = x2) -> x0 = (x1 x2)) = (True -> x3).
Definition term51 (a0 : Type') (x0 : a0) := (fun y0 : Prop => y0 = True) (exists y0 : a0, y0 = x0).
Definition term30 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : a0, (y0 = x2) -> x0 = (x1 x2).
Definition term11 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) := forall y0 : a0, (y0 = x0) -> x1 = (x2 y0).
Definition term56 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := True -> (x0 = (x1 x2)) = (x0 = (x1 x2)).
Definition term37 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : a0 => y0 = x3) x0) -> x1 = (x2 x3).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (y0 = x1) -> x0 x1.
Definition term40 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (forall y0 : a0, (y0 = x2) -> x0 = (x1 x2)).
Definition term39 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (forall y0 : a0, ((fun y1 : a0 => y1 = x2) y0) -> x0 = (x1 x2)).
Definition term23 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) (x4 : Prop) := ((x2 = x3) -> (x0 = (x1 x2)) = x4) -> ((x2 = x3) -> x0 = (x1 x2)) = ((x2 = x3) -> x4).
Definition term52 (a0 : Type') (x0 : a0) := @eq Prop ((fun y0 : Prop => y0 = True) (exists y0 : a0, y0 = x0)).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := True -> (x0 x1) = (x0 x1).
Definition term59 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := ((forall y0 : a0, (y0 = x2) -> x0 = (x1 y0)) = (x0 = (x1 x2))) -> ((x0 = (x1 x2)) -> (x0 = (forall y0 : a0, (y0 = x2) -> x1 y0)) = x3) -> ((forall y0 : a0, (y0 = x2) -> x0 = (x1 y0)) -> x0 = (forall y0 : a0, (y0 = x2) -> x1 y0)) = ((x0 = (x1 x2)) -> x3).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (True -> (x0 x1) = (x0 x1)) -> ((exists y0 : a0, y0 = x1) -> x0 x1) = (True -> x0 x1).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := ((x1 = x2) = (x1 = x2)) -> ((x1 = x2) -> (x0 x1) = x3) -> ((x1 = x2) -> x0 x1) = ((x1 = x2) -> x3).
Definition term60 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := ((x0 = (x1 x2)) -> (x0 = (forall y0 : a0, (y0 = x2) -> x1 y0)) = x3) -> ((forall y0 : a0, (y0 = x2) -> x0 = (x1 y0)) -> x0 = (forall y0 : a0, (y0 = x2) -> x1 y0)) = ((x0 = (x1 x2)) -> x3).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (y0 = x0) -> x1 y0.
Definition term24 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) := (x0 = x3) -> (x1 = (x2 x0)) = (x1 = (x2 x3)).
Definition term21 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) (x4 : Prop) (x5 : Prop) := ((x3 = x0) = x4) -> (x4 -> (x1 = (x2 x3)) = x5) -> ((x3 = x0) -> x1 = (x2 x3)) = (x4 -> x5).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y1 = y0) x0.
Definition term93 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> Prop) := (x0 = (x2 x1)) -> (x0 = (forall y0 : a0, (y0 = x1) -> x2 y0)) = True.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := ((x1 = x2) -> (x0 x1) = x3) -> ((x1 = x2) -> x0 x1) = ((x1 = x2) -> x3).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (exists y0 : a0, y0 = x1) -> x0 x1.
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term63 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x2 = x0) = y0) -> (y0 -> (x1 x2) = y1) -> ((x2 = x0) -> x1 x2) = (y0 -> y1)) x3.
Definition term47 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((exists y2 : a0, y2 = x2) = y0) -> (y0 -> (x0 = (x1 x2)) = y1) -> ((exists y2 : a0, y2 = x2) -> x0 = (x1 x2)) = (y0 -> y1)) x3.
Definition term13 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((forall y2 : a0, (y2 = x1) -> x0 = (x2 y2)) = y0) -> (y0 -> (x0 = (forall y2 : a0, (y2 = x1) -> x2 y2)) = y1) -> ((forall y2 : a0, (y2 = x1) -> x0 = (x2 y2)) -> x0 = (forall y2 : a0, (y2 = x1) -> x2 y2)) = (y0 -> y1)) x3.
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((fun y0 : a0 => y0 = x2) x0) -> x1 x2.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => (forall y1 : a0, (x0 y1) -> y0) = ((exists y1 : a0, x0 y1) -> y0)) x1.
Definition term50 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) (x4 : Prop) := ((exists y0 : a0, y0 = x2) = x3) -> (x3 -> (x0 = (x1 x2)) = x4) -> ((exists y0 : a0, y0 = x2) -> x0 = (x1 x2)) = (x3 -> x4).
Definition term16 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) (x4 : Prop) := ((forall y0 : a0, (y0 = x1) -> x0 = (x2 y0)) = x3) -> (x3 -> (x0 = (forall y0 : a0, (y0 = x1) -> x2 y0)) = x4) -> ((forall y0 : a0, (y0 = x1) -> x0 = (x2 y0)) -> x0 = (forall y0 : a0, (y0 = x1) -> x2 y0)) = (x3 -> x4).
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term66 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) (x4 : Prop) := ((x2 = x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((x2 = x0) -> x1 x2) = (x3 -> x4).
Definition term95 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> Prop) := (forall y0 : a0, (y0 = x1) -> x0 = (x2 y0)) -> x0 = (forall y0 : a0, (y0 = x1) -> x2 y0).
Definition term96 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 = (x1 x2)) -> True.
Definition term44 (a0 : Type') (x0 : a0) := imp (exists y0 : a0, y0 = x0).
Definition term42 (a0 : Type') (x0 : a0) := exists y0 : a0, (fun y1 : a0 => y1 = x0) y0.
Definition term94 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 = (x1 x2)) -> (x0 = (forall y0 : a0, (y0 = x2) -> x1 y0)) = True) -> ((forall y0 : a0, (y0 = x2) -> x0 = (x1 y0)) -> x0 = (forall y0 : a0, (y0 = x2) -> x1 y0)) = ((x0 = (x1 x2)) -> True).
Definition term53 (a0 : Type') (x0 : a0) := @eq Prop ((exists y0 : a0, y0 = x0) = True).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((exists y1 : a0, y1 = x1) = x2) -> (x2 -> (x0 x1) = y0) -> ((exists y1 : a0, y1 = x1) -> x0 x1) = (x2 -> y0)) x3.
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, ((fun y1 : a0 => y1 = x1) y0) -> x0 x1.
Definition term41 (a0 : Type') (x0 : a0) := fun y0 : a0 => (fun y1 : a0 => y1 = x0) y0.
Definition term29 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => (y0 = x2) -> x0 = (x1 x2).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, (forall y2 : a0, (y0 y2) -> y1) = ((exists y2 : a0, y0 y2) -> y1)) x0.
Definition term43 (a0 : Type') (x0 : a0) := imp (exists y0 : a0, (fun y1 : a0 => y1 = x0) y0).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := forall y0 : Prop, ((exists y1 : a0, y1 = x1) = x2) -> (x2 -> (x0 x1) = y0) -> ((exists y1 : a0, y1 = x1) -> x0 x1) = (x2 -> y0).
Definition term64 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := forall y0 : Prop, ((x2 = x0) = x3) -> (x3 -> (x1 x2) = y0) -> ((x2 = x0) -> x1 x2) = (x3 -> y0).
Definition term48 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := forall y0 : Prop, ((exists y1 : a0, y1 = x2) = x3) -> (x3 -> (x0 = (x1 x2)) = y0) -> ((exists y1 : a0, y1 = x2) -> x0 = (x1 x2)) = (x3 -> y0).
Definition term19 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) (x4 : Prop) := forall y0 : Prop, ((x3 = x0) = x4) -> (x4 -> (x1 = (x2 x3)) = y0) -> ((x3 = x0) -> x1 = (x2 x3)) = (x4 -> y0).
Definition term14 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := forall y0 : Prop, ((forall y1 : a0, (y1 = x1) -> x0 = (x2 y1)) = x3) -> (x3 -> (x0 = (forall y1 : a0, (y1 = x1) -> x2 y1)) = y0) -> ((forall y1 : a0, (y1 = x1) -> x0 = (x2 y1)) -> x0 = (forall y1 : a0, (y1 = x1) -> x2 y1)) = (x3 -> y0).
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term1 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0) := imp ((fun y0 : a0 => y0 = x0) x1).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : Prop, forall y1 : Prop, ((exists y2 : a0, y2 = x1) = y0) -> (y0 -> (x0 x1) = y1) -> ((exists y2 : a0, y2 = x1) -> x0 x1) = (y0 -> y1).
Definition term62 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, ((x2 = x0) = y0) -> (y0 -> (x1 x2) = y1) -> ((x2 = x0) -> x1 x2) = (y0 -> y1).
Definition term46 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, ((exists y2 : a0, y2 = x2) = y0) -> (y0 -> (x0 = (x1 x2)) = y1) -> ((exists y2 : a0, y2 = x2) -> x0 = (x1 x2)) = (y0 -> y1).
Definition term17 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) := forall y0 : Prop, forall y1 : Prop, ((x3 = x0) = y0) -> (y0 -> (x1 = (x2 x3)) = y1) -> ((x3 = x0) -> x1 = (x2 x3)) = (y0 -> y1).
Definition term10 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((forall y2 : a0, (y2 = x1) -> x0 = (x2 y2)) = y0) -> (y0 -> (x0 = (forall y2 : a0, (y2 = x1) -> x2 y2)) = y1) -> ((forall y2 : a0, (y2 = x1) -> x0 = (x2 y2)) -> x0 = (forall y2 : a0, (y2 = x1) -> x2 y2)) = (y0 -> y1).
Definition term9 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term33 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term71 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) -> x1 x2.
Definition term31 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := forall y0 : a0, ((fun y1 : a0 => y1 = x2) y0) -> x0 = (x1 x2).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := (True -> (x0 x1) = x2) -> ((exists y0 : a0, y0 = x1) -> x0 x1) = (True -> x2).
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((x2 = x0) = x3) -> (x3 -> (x1 x2) = y0) -> ((x2 = x0) -> x1 x2) = (x3 -> y0)) x4.
Definition term49 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((exists y1 : a0, y1 = x2) = x3) -> (x3 -> (x0 = (x1 x2)) = y0) -> ((exists y1 : a0, y1 = x2) -> x0 = (x1 x2)) = (x3 -> y0)) x4.
Definition term15 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((forall y1 : a0, (y1 = x1) -> x0 = (x2 y1)) = x3) -> (x3 -> (x0 = (forall y1 : a0, (y1 = x1) -> x2 y1)) = y0) -> ((forall y1 : a0, (y1 = x1) -> x0 = (x2 y1)) -> x0 = (forall y1 : a0, (y1 = x1) -> x2 y1)) = (x3 -> y0)) x4.
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0) := imp (x0 = x1).
Definition term72 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 = x2) -> x1 x2.
Definition term70 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x0 = x2) -> (x1 x0) = (x1 x2)) -> ((x0 = x2) -> x1 x0) = ((x0 = x2) -> x1 x2).
Definition term20 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((x3 = x0) = x4) -> (x4 -> (x1 = (x2 x3)) = y0) -> ((x3 = x0) -> x1 = (x2 x3)) = (x4 -> y0)) x5.
Definition term73 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (y0 = x0) -> x1 y0.
Definition term32 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, (fun y1 : a0 => y1 = x2) y0) -> x0 = (x1 x2).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (exists y0 : a0, (fun y1 : a0 => y1 = x1) y0) -> x0 x1.
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((fun y1 : a0 => y1 = x1) y0) -> x0 x1.
Definition term58 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := True -> x0 = (x1 x2).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, (forall y1 : a0, (x0 y1) -> y0) = ((exists y1 : a0, x0 y1) -> y0).
Definition term27 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) := (x0 = x3) -> x1 = (x2 x3).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := True -> x0 x1.
Definition term54 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := ((exists y0 : a0, y0 = x2) = True) -> (True -> (x0 = (x1 x2)) = x3) -> ((exists y0 : a0, y0 = x2) -> x0 = (x1 x2)) = (True -> x3).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (y0 = x1) -> x0 x1.
Definition term38 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => ((fun y1 : a0 => y1 = x2) y0) -> x0 = (x1 x2).
Definition term69 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 = x2) -> (x1 x0) = (x1 x2).
Definition term25 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) := ((x0 = x3) -> (x1 = (x2 x0)) = (x1 = (x2 x3))) -> ((x0 = x3) -> x1 = (x2 x0)) = ((x0 = x3) -> x1 = (x2 x3)).
Definition term22 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) (x4 : Prop) := ((x2 = x3) = (x2 = x3)) -> ((x2 = x3) -> (x0 = (x1 x2)) = x4) -> ((x2 = x3) -> x0 = (x1 x2)) = ((x2 = x3) -> x4).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := ((exists y0 : a0, y0 = x1) = True) -> (True -> (x0 x1) = x2) -> ((exists y0 : a0, y0 = x1) -> x0 x1) = (True -> x2).
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => y0 = x0) x1.
Definition term18 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x3 = x0) = y0) -> (y0 -> (x1 = (x2 x3)) = y1) -> ((x3 = x0) -> x1 = (x2 x3)) = (y0 -> y1)) x4.
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (forall y0 : a0, (y0 = x1) -> x0 x1).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (forall y0 : a0, ((fun y1 : a0 => y1 = x1) y0) -> x0 x1).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((exists y2 : a0, y2 = x1) = y0) -> (y0 -> (x0 x1) = y1) -> ((exists y2 : a0, y2 = x1) -> x0 x1) = (y0 -> y1)) x2.
Definition term57 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := (True -> (x0 = (x1 x2)) = (x0 = (x1 x2))) -> ((exists y0 : a0, y0 = x2) -> x0 = (x1 x2)) = (True -> x0 = (x1 x2)).
Definition term28 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (y0 = x0) -> x1 = (x2 y0).
Definition term45 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, y0 = x2) -> x0 = (x1 x2).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) (x3 : Prop) := ((exists y0 : a0, y0 = x1) = x2) -> (x2 -> (x0 x1) = x3) -> ((exists y0 : a0, y0 = x1) -> x0 x1) = (x2 -> x3).
