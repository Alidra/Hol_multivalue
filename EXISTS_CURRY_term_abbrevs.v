Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term56 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : type333 a0 a1 a2 => (exists y1 : type1228 a0 a1 a2, y0 y1) = (exists y1 : type1518 a0 a1 a2, y0 (@GABS ((prod a2 a1) -> a0) (fun y2 : type1228 a0 a1 a2 => forall y3 : a2, forall y4 : a1, @GEQ a0 (y2 (@pair a2 a1 y3 y4)) (y1 y3 y4)))).
Definition term43 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : type1228 a0 a1 a2) (x2 : a2) := fun y0 : a1 => @GEQ a0 (x0 (@pair a2 a1 x2 y0)) (x1 (@pair a2 a1 x2 y0)).
Definition term34 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := (fun y0 : a1 => (fun y1 : a1 => x0 (@pair a2 a1 x1 y1)) y0) x2.
Definition term29 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) := @eq (a1 -> a0) ((fun y0 : a2 => (fun y1 : a2 => fun y2 : a1 => x0 (@pair a2 a1 y1 y2)) y0) x1).
Definition term31 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := (fun y0 : a2 => fun y1 : a1 => x0 (@pair a2 a1 y0 y1)) x1 x2.
Definition term60 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term52 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) := @GABS ((prod a2 a1) -> a0) (fun y0 : type1228 a0 a1 a2 => forall y1 : a2, forall y2 : a1, @GEQ a0 (y0 (@pair a2 a1 y1 y2)) ((fun y3 : a2 => fun y4 : a1 => x0 (@pair a2 a1 y3 y4)) y1 y2)).
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) := @GABS ((prod a2 a1) -> a0) (fun y0 : type1228 a0 a1 a2 => forall y1 : a2, forall y2 : a1, @GEQ a0 (y0 (@pair a2 a1 y1 y2)) (x0 (@pair a2 a1 y1 y2))).
Definition term38 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := @eq a0 ((fun y0 : a1 => x0 (@pair a2 a1 x1 y0)) x2).
Definition term44 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : type1228 a0 a1 a2) (x2 : a2) := forall y0 : a1, @GEQ a0 (x0 (@pair a2 a1 x2 y0)) ((fun y1 : a2 => fun y2 : a1 => x1 (@pair a2 a1 y1 y2)) x2 y0).
Definition term54 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := exists y0 : type1228 a0 a1 a2, x0 y0.
Definition term41 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : type1228 a0 a1 a2) (x2 : a2) (x3 : a1) := @GEQ a0 (x0 (@pair a2 a1 x2 x3)) (x1 (@pair a2 a1 x2 x3)).
Definition term51 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) := fun y0 : type1228 a0 a1 a2 => forall y1 : a2, forall y2 : a1, @GEQ a0 (y0 (@pair a2 a1 y1 y2)) (x0 (@pair a2 a1 y1 y2)).
Definition term50 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) := fun y0 : type1228 a0 a1 a2 => forall y1 : a2, forall y2 : a1, @GEQ a0 (y0 (@pair a2 a1 y1 y2)) ((fun y3 : a2 => fun y4 : a1 => x0 (@pair a2 a1 y3 y4)) y1 y2).
Definition term35 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := x0 (@pair a2 a1 x1 x2).
Definition term10 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := fun y0 : type1518 a0 a1 a2 => x0 (@GABS ((prod a2 a1) -> a0) (fun y1 : type1228 a0 a1 a2 => forall y2 : a2, forall y3 : a1, @GEQ a0 (y1 (@pair a2 a1 y2 y3)) (y0 y2 y3))).
Definition term26 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) := fun y0 : a2 => fun y1 : a1 => x0 (@pair a2 a1 y0 y1).
Definition term30 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) := @eq (a1 -> a0) ((fun y0 : a2 => fun y1 : a1 => x0 (@pair a2 a1 y0 y1)) x1).
Definition term11 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) (x1 : type1518 a0 a1 a2) := (fun y0 : type1518 a0 a1 a2 => x0 (@GABS ((prod a2 a1) -> a0) (fun y1 : type1228 a0 a1 a2 => forall y2 : a2, forall y3 : a1, @GEQ a0 (y1 (@pair a2 a1 y2 y3)) (y0 y2 y3)))) x1.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) := (fun y0 : type1228 a0 a1 a2 => (@GABS ((prod a2 a1) -> a0) (fun y1 : type1228 a0 a1 a2 => forall y2 : a2, forall y3 : a1, @GEQ a0 (y1 (@pair a2 a1 y2 y3)) (y0 (@pair a2 a1 y2 y3)))) = y0) x0.
Definition term17 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) (x1 : type1228 a0 a1 a2) := (fun y0 : type1518 a0 a1 a2 => x0 (@GABS ((prod a2 a1) -> a0) (fun y1 : type1228 a0 a1 a2 => forall y2 : a2, forall y3 : a1, @GEQ a0 (y1 (@pair a2 a1 y2 y3)) (y0 y2 y3)))) (fun y0 : a2 => fun y1 : a1 => x1 (@pair a2 a1 y0 y1)).
Definition term14 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := exists y0 : type1518 a0 a1 a2, x0 (@GABS ((prod a2 a1) -> a0) (fun y1 : type1228 a0 a1 a2 => forall y2 : a2, forall y3 : a1, @GEQ a0 (y1 (@pair a2 a1 y2 y3)) (y0 y2 y3))).
Definition term32 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := (fun y0 : a1 => x0 (@pair a2 a1 x1 y0)) x2.
Definition term13 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := fun y0 : type1518 a0 a1 a2 => (fun y1 : type1518 a0 a1 a2 => x0 (@GABS ((prod a2 a1) -> a0) (fun y2 : type1228 a0 a1 a2 => forall y3 : a2, forall y4 : a1, @GEQ a0 (y2 (@pair a2 a1 y3 y4)) (y1 y3 y4)))) y0.
Definition term53 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := fun y0 : type1228 a0 a1 a2 => x0 y0.
Definition term23 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1518 a0 a1 a2) (x1 : a2) := (fun y0 : a2 => x0 y0) x1.
Definition term36 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) := fun y0 : a1 => (fun y1 : a1 => x0 (@pair a2 a1 x1 y1)) y0.
Definition term28 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) := fun y0 : a2 => (fun y1 : a2 => fun y2 : a1 => x0 (@pair a2 a1 y1 y2)) y0.
Definition term46 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : type1228 a0 a1 a2) := fun y0 : a2 => forall y1 : a1, @GEQ a0 (x0 (@pair a2 a1 y0 y1)) ((fun y2 : a2 => fun y3 : a1 => x1 (@pair a2 a1 y2 y3)) y0 y1).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term21 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := exists y0 : type1228 a0 a1 a2, x0 (@GABS ((prod a2 a1) -> a0) (fun y1 : type1228 a0 a1 a2 => forall y2 : a2, forall y3 : a1, @GEQ a0 (y1 (@pair a2 a1 y2 y3)) ((fun y4 : a2 => fun y5 : a1 => y0 (@pair a2 a1 y4 y5)) y2 y3))).
Definition term59 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type333 a0 a1 a2, True.
Definition term45 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : type1228 a0 a1 a2) (x2 : a2) := forall y0 : a1, @GEQ a0 (x0 (@pair a2 a1 x2 y0)) (x1 (@pair a2 a1 x2 y0)).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type443 a0 a1 a2) := (fun y0 : type443 a0 a1 a2 => (exists y1 : type1412 a0 a1 a2, y0 y1) = (exists y1 : type1209 a0 a1 a2, y0 (fun y2 : a0 => fun y3 : a1 => y1 (@pair a0 a1 y2 y3)))) x0.
Definition term18 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) (x1 : type1228 a0 a1 a2) := x0 (@GABS ((prod a2 a1) -> a0) (fun y0 : type1228 a0 a1 a2 => forall y1 : a2, forall y2 : a1, @GEQ a0 (y0 (@pair a2 a1 y1 y2)) ((fun y3 : a2 => fun y4 : a1 => x1 (@pair a2 a1 y3 y4)) y1 y2))).
Definition term12 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) (x1 : type1518 a0 a1 a2) := x0 (@GABS ((prod a2 a1) -> a0) (fun y0 : type1228 a0 a1 a2 => forall y1 : a2, forall y2 : a1, @GEQ a0 (y0 (@pair a2 a1 y1 y2)) (x1 y1 y2))).
Definition term19 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := fun y0 : type1228 a0 a1 a2 => (fun y1 : type1518 a0 a1 a2 => x0 (@GABS ((prod a2 a1) -> a0) (fun y2 : type1228 a0 a1 a2 => forall y3 : a2, forall y4 : a1, @GEQ a0 (y2 (@pair a2 a1 y3 y4)) (y1 y3 y4)))) (fun y1 : a2 => fun y2 : a1 => y0 (@pair a2 a1 y1 y2)).
Definition term47 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : type1228 a0 a1 a2) := fun y0 : a2 => forall y1 : a1, @GEQ a0 (x0 (@pair a2 a1 y0 y1)) (x1 (@pair a2 a1 y0 y1)).
Definition term15 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := @eq Prop (exists y0 : type1518 a0 a1 a2, (fun y1 : type1518 a0 a1 a2 => x0 (@GABS ((prod a2 a1) -> a0) (fun y2 : type1228 a0 a1 a2 => forall y3 : a2, forall y4 : a1, @GEQ a0 (y2 (@pair a2 a1 y3 y4)) (y1 y3 y4)))) y0).
Definition term20 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := fun y0 : type1228 a0 a1 a2 => x0 (@GABS ((prod a2 a1) -> a0) (fun y1 : type1228 a0 a1 a2 => forall y2 : a2, forall y3 : a1, @GEQ a0 (y1 (@pair a2 a1 y2 y3)) ((fun y4 : a2 => fun y5 : a1 => y0 (@pair a2 a1 y4 y5)) y2 y3))).
Definition term39 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := @GEQ a0 (x0 (@pair a2 a1 x1 x2)).
Definition term24 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) := (fun y0 : a2 => (fun y1 : a2 => fun y2 : a1 => x0 (@pair a2 a1 y1 y2)) y0) x1.
Definition term16 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := @eq Prop (exists y0 : type1518 a0 a1 a2, x0 (@GABS ((prod a2 a1) -> a0) (fun y1 : type1228 a0 a1 a2 => forall y2 : a2, forall y3 : a1, @GEQ a0 (y1 (@pair a2 a1 y2 y3)) (y0 y2 y3)))).
Definition term40 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : type1228 a0 a1 a2) (x2 : a2) (x3 : a1) := @GEQ a0 (x0 (@pair a2 a1 x2 x3)) ((fun y0 : a2 => fun y1 : a1 => x1 (@pair a2 a1 y0 y1)) x2 x3).
Definition term9 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := exists y0 : type1228 a0 a1 a2, (fun y1 : type1518 a0 a1 a2 => x0 (@GABS ((prod a2 a1) -> a0) (fun y2 : type1228 a0 a1 a2 => forall y3 : a2, forall y4 : a1, @GEQ a0 (y2 (@pair a2 a1 y3 y4)) (y1 y3 y4)))) (fun y1 : a2 => fun y2 : a1 => y0 (@pair a2 a1 y1 y2)).
Definition term25 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) := (fun y0 : a2 => fun y1 : a1 => x0 (@pair a2 a1 y0 y1)) x1.
Definition term42 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : type1228 a0 a1 a2) (x2 : a2) := fun y0 : a1 => @GEQ a0 (x0 (@pair a2 a1 x2 y0)) ((fun y1 : a2 => fun y2 : a1 => x1 (@pair a2 a1 y1 y2)) x2 y0).
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type876 a0 a1 a2) := exists y0 : type1518 a0 a1 a2, x0 y0.
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type443 a0 a1 a2) := exists y0 : type1412 a0 a1 a2, x0 y0.
Definition term57 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : type333 a0 a1 a2 => True.
Definition term37 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := @eq a0 ((fun y0 : a1 => (fun y1 : a1 => x0 (@pair a2 a1 x1 y1)) y0) x2).
Definition term55 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := @eq Prop (exists y0 : type1228 a0 a1 a2, x0 y0).
Definition term61 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : Prop) := forall y0 : type333 a0 a1 a2, x0.
Definition term58 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type333 a0 a1 a2, (exists y1 : type1228 a0 a1 a2, y0 y1) = (exists y1 : type1518 a0 a1 a2, y0 (@GABS ((prod a2 a1) -> a0) (fun y2 : type1228 a0 a1 a2 => forall y3 : a2, forall y4 : a1, @GEQ a0 (y2 (@pair a2 a1 y3 y4)) (y1 y3 y4)))).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type1228 a0 a1 a2, (@GABS ((prod a2 a1) -> a0) (fun y1 : type1228 a0 a1 a2 => forall y2 : a2, forall y3 : a1, @GEQ a0 (y1 (@pair a2 a1 y2 y3)) (y0 (@pair a2 a1 y2 y3)))) = y0.
Definition term49 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : type1228 a0 a1 a2) := forall y0 : a2, forall y1 : a1, @GEQ a0 (x0 (@pair a2 a1 y0 y1)) (x1 (@pair a2 a1 y0 y1)).
Definition term48 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : type1228 a0 a1 a2) := forall y0 : a2, forall y1 : a1, @GEQ a0 (x0 (@pair a2 a1 y0 y1)) ((fun y2 : a2 => fun y3 : a1 => x1 (@pair a2 a1 y2 y3)) y0 y1).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) := (fun y0 : a1 => x0 y0) x1.
Definition term8 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type333 a0 a1 a2) := exists y0 : type1518 a0 a1 a2, (fun y1 : type1518 a0 a1 a2 => x0 (@GABS ((prod a2 a1) -> a0) (fun y2 : type1228 a0 a1 a2 => forall y3 : a2, forall y4 : a1, @GEQ a0 (y2 (@pair a2 a1 y3 y4)) (y1 y3 y4)))) y0.
Definition term27 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) := fun y0 : a1 => x0 (@pair a2 a1 x1 y0).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type876 a0 a1 a2) := exists y0 : type1228 a0 a1 a2, x0 (fun y1 : a2 => fun y2 : a1 => y0 (@pair a2 a1 y1 y2)).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type443 a0 a1 a2) := exists y0 : type1209 a0 a1 a2, x0 (fun y1 : a0 => fun y2 : a1 => y0 (@pair a0 a1 y1 y2)).