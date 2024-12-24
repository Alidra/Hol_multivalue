Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term64 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) := real_le (real_abs (x0 x2)) (x1 x2).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 x0) -> real_le ((fun y1 : a0 => real_abs (x1 y1)) y0) (x2 y0).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_abs (@sum a0 x0 x1).
Definition term59 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @eq real ((fun y0 : a0 => (fun y1 : a0 => real_abs (x0 y1)) y0) x1).
Definition term71 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term80 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (real_abs (y0 y3)) (y1 y3))) -> real_le (real_abs (@sum a0 y2 y0)) (@sum a0 y2 y1).
Definition term12 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ (forall y3 : a0, (@IN a0 y3 y1) -> real_le (y0 y3) (y2 y3))) -> real_le (@sum a0 y1 y0) (@sum a0 y1 y2).
Definition term0 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (y0 y3) (y1 y3))) -> real_le (@sum a0 y2 y0) (@sum a0 y2 y1).
Definition term31 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term26 (x0 : real) (x1 : real) := exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> real_le ((fun y1 : a0 => real_abs (x1 y1)) y0) (x2 y0).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_abs (x1 y0)) (x2 y0).
Definition term27 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 y0) /\ (real_le y0 x1).
Definition term70 (a0 : Type') := forall y0 : a0, True.
Definition term14 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ (forall y3 : a0, (@IN a0 y3 y1) -> real_le (y0 y3) (y2 y3))) -> real_le (@sum a0 y1 y0) (@sum a0 y1 y2)) x0.
Definition term1 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (y0 y3) (y1 y3))) -> real_le (@sum a0 y2 y0) (@sum a0 y2 y1)) x0.
Definition term16 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (fun y0 : a0 -> real => ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) (y0 y1))) -> real_le (@sum a0 x1 x0) (@sum a0 x1 y0)) x2.
Definition term5 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> real_le (x0 y1) (x1 y1))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 x1)) x2.
Definition term60 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @eq real ((fun y0 : a0 => real_abs (x0 y0)) x1).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 x0) -> real_le (real_abs (x1 x3)) (x2 x3).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> real_le (real_abs (x1 y0)) (x2 y0)) x3.
Definition term39 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> real_le (real_abs (@sum a0 y0 x0)) (@sum a0 y0 (fun y1 : a0 => real_abs (x0 y1))).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := and (real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0)))).
Definition term13 (a0 : Type') := (forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (y0 y3) (y1 y3))) -> real_le (@sum a0 y2 y0) (@sum a0 y2 y1)) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ (forall y3 : a0, (@IN a0 y3 y1) -> real_le (y0 y3) (y2 y3))) -> real_le (@sum a0 y1 y0) (@sum a0 y1 y2).
Definition term77 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (real_abs (x0 y0)) (x2 y0))) -> real_le (real_abs (@sum a0 x1 x0)) (@sum a0 x1 x2).
Definition term61 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_le ((fun y0 : a0 => real_abs (x0 y0)) x1).
Definition term76 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_le (real_abs (@sum a0 x1 x0)) (@sum a0 x1 x2).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 x0) -> real_le ((fun y0 : a0 => real_abs (x1 y0)) x3) (x2 x3).
Definition term30 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term19 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term17 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@FINITE a0 x0) -> (real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0)))) = True.
Definition term23 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term15 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> real, ((@FINITE a0 y0) /\ (forall y2 : a0, (@IN a0 y2 y0) -> real_le (x0 y2) (y1 y2))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 y1)) x1.
Definition term3 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> real_le (x0 y2) (y0 y2))) -> real_le (@sum a0 y1 x0) (@sum a0 y1 y0)) x1.
Definition term74 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := fun y0 : real => (real_le (real_abs (@sum a0 x1 x0)) y0) /\ (real_le y0 (@sum a0 x1 x2)).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term62 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_le (real_abs (x0 x1)).
Definition term45 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_le (@sum a0 x1 (fun y0 : a0 => real_abs (x0 y0))) (@sum a0 x1 x2).
Definition term25 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> real_le x0 x1.
Definition term29 (x0 : real) := forall y0 : real, (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0.
Definition term48 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le ((fun y1 : a0 => real_abs (x0 y1)) y0) (x2 y0))) -> real_le (@sum a0 x1 (fun y0 : a0 => real_abs (x0 y0))) (@sum a0 x1 x2).
Definition term28 (x0 : real) (x1 : real) := (exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1)) -> real_le x0 x1.
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term68 (a0 : Type') := fun y0 : a0 => True.
Definition term54 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term73 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := exists y0 : real, (real_le (real_abs (@sum a0 x1 x0)) y0) /\ (real_le y0 (@sum a0 x1 x2)).
Definition term49 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 => real_abs (x0 y0).
Definition term9 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (y0 y3) (y1 y3))) -> real_le (@sum a0 y2 y0) (@sum a0 y2 y1)) -> real_le (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term8 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_le (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_abs (x1 y0)).
Definition term32 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1) x0.
Definition term38 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> real_le (real_abs (@sum a0 y1 y0)) (@sum a0 y1 (fun y2 : a0 => real_abs (y0 y2)))) x0.
Definition term40 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> real_le (real_abs (@sum a0 y0 x0)) (@sum a0 y0 (fun y1 : a0 => real_abs (x0 y1)))) x1.
Definition term57 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_abs (x0 x1).
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term20 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1) x1.
Definition term79 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> real_le (real_abs (x0 y2)) (y0 y2))) -> real_le (real_abs (@sum a0 y1 x0)) (@sum a0 y1 y0).
Definition term11 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, forall y1 : a0 -> real, ((@FINITE a0 y0) /\ (forall y2 : a0, (@IN a0 y2 y0) -> real_le (x0 y2) (y1 y2))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 y1).
Definition term2 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> real_le (x0 y2) (y0 y2))) -> real_le (@sum a0 y1 x0) (@sum a0 y1 y0).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@FINITE a0 x0) -> real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0))).
Definition term22 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0) x2.
Definition term36 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (exists y0 : real, (real_le (real_abs (@sum a0 x1 x0)) y0) /\ (real_le y0 (@sum a0 x1 x2))) -> real_le (real_abs (@sum a0 x1 x0)) (@sum a0 x1 x2).
Definition term33 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0) x1.
Definition term6 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) (x2 y0))) -> real_le (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term46 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (real_le (real_abs (@sum a0 x1 x0)) (@sum a0 x1 (fun y0 : a0 => real_abs (x0 y0)))) /\ (real_le (@sum a0 x1 (fun y0 : a0 => real_abs (x0 y0))) (@sum a0 x1 x2)).
Definition term21 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le ((fun y1 : a0 => real_abs (x1 y1)) y0) (x2 y0)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_abs (x1 y0)) (x2 y0)).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) (x2 y0)).
Definition term24 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term63 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) := real_le ((fun y0 : a0 => real_abs (x0 y0)) x2) (x1 x2).
Definition term47 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := True /\ (real_le (@sum a0 x1 (fun y0 : a0 => real_abs (x0 y0))) (@sum a0 x1 x2)).
Definition term58 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 => (fun y1 : a0 => real_abs (x0 y1)) y0.
Definition term56 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => real_abs (x0 y0)) x1.
Definition term78 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> real_le (real_abs (x0 y1)) (x1 y1))) -> real_le (real_abs (@sum a0 y0 x0)) (@sum a0 y0 x1).
Definition term10 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := forall y0 : a0 -> real, ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) (y0 y1))) -> real_le (@sum a0 x1 x0) (@sum a0 x1 y0).
Definition term4 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> real_le (x0 y1) (x1 y1))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 x1).
Definition term55 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => real_abs (x0 y1)) y0) x1.
Definition term18 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) x0.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0))).
