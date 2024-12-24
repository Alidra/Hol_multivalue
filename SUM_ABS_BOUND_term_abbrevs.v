Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term79 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := fun y0 : real => (real_le (real_abs (@sum a0 x1 x0)) y0) /\ (real_le y0 (real_mul (real_of_num (@CARD a0 x1)) x2)).
Definition term54 (a0 : Type') (x0 : a0 -> real) (x1 : real) (x2 : a0) (x3 : a0 -> Prop) (x4 : Prop) := ((@IN a0 x2 x3) -> (real_le ((fun y0 : a0 => real_abs (x0 y0)) x2) x1) = x4) -> ((@IN a0 x2 x3) -> real_le ((fun y0 : a0 => real_abs (x0 y0)) x2) x1) = ((@IN a0 x2 x3) -> x4).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := real_mul (real_of_num (@CARD a0 x0)) x1.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := forall y0 : a0, (@IN a0 y0 x0) -> real_le ((fun y1 : a0 => real_abs (x1 y1)) y0) x2.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_abs (x1 y0)) x2.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_abs (@sum a0 x0 x1).
Definition term61 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @eq real ((fun y0 : a0 => (fun y1 : a0 => real_abs (x0 y1)) y0) x1).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> real_le (real_abs (x1 y0)) x2) x3.
Definition term74 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term48 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : real) := real_le ((fun y0 : a0 => real_abs (x0 y0)) x1) x2.
Definition term85 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> real, forall y2 : real, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> real_le (real_abs (y1 y3)) y2)) -> real_le (real_abs (@sum a0 y0 y1)) (real_mul (real_of_num (@CARD a0 y0)) y2).
Definition term14 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term9 (x0 : real) (x1 : real) := exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1).
Definition term10 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 y0) /\ (real_le y0 x1).
Definition term67 (a0 : Type') (x0 : a0 -> real) (x1 : real) (x2 : a0) (x3 : a0 -> Prop) := ((@IN a0 x2 x3) -> (real_le ((fun y0 : a0 => real_abs (x0 y0)) x2) x1) = True) -> ((@IN a0 x2 x3) -> real_le ((fun y0 : a0 => real_abs (x0 y0)) x2) x1) = ((@IN a0 x2 x3) -> True).
Definition term73 (a0 : Type') := forall y0 : a0, True.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> real, forall y2 : real, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> real_le (y1 y3) y2)) -> real_le (@sum a0 y0 y1) (real_mul (real_of_num (@CARD a0 y0)) y2)) x0.
Definition term62 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @eq real ((fun y0 : a0 => real_abs (x0 y0)) x1).
Definition term69 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> True.
Definition term23 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> real_le (real_abs (@sum a0 y0 x0)) (@sum a0 y0 (fun y1 : a0 => real_abs (x0 y1))).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := and (real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0)))).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) (x4 : Prop) (x5 : Prop) := ((@IN a0 x2 x0) = x4) -> (x4 -> (real_le ((fun y0 : a0 => real_abs (x1 y0)) x2) x3) = x5) -> ((@IN a0 x2 x0) -> real_le ((fun y0 : a0 => real_abs (x1 y0)) x2) x3) = (x4 -> x5).
Definition term63 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_le ((fun y0 : a0 => real_abs (x0 y0)) x1).
Definition term13 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term2 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term0 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term53 (a0 : Type') (x0 : a0 -> real) (x1 : real) (x2 : a0) (x3 : a0 -> Prop) (x4 : Prop) := ((@IN a0 x2 x3) = (@IN a0 x2 x3)) -> ((@IN a0 x2 x3) -> (real_le ((fun y0 : a0 => real_abs (x0 y0)) x2) x1) = x4) -> ((@IN a0 x2 x3) -> real_le ((fun y0 : a0 => real_abs (x0 y0)) x2) x1) = ((@IN a0 x2 x3) -> x4).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@FINITE a0 x0) -> (real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0)))) = True.
Definition term6 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : real, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> real_le (y0 y2) y1)) -> real_le (@sum a0 x0 y0) (real_mul (real_of_num (@CARD a0 x0)) y1)) x1.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) := (@IN a0 x2 x0) -> real_le (real_abs (x1 x2)) x3.
Definition term83 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := forall y0 : real, ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (real_abs (x0 y1)) y0)) -> real_le (real_abs (@sum a0 x1 x0)) (real_mul (real_of_num (@CARD a0 x1)) y0).
Definition term30 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := forall y0 : real, ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) y0)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) y0).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) := (@IN a0 x2 x0) -> (real_le ((fun y0 : a0 => real_abs (x1 y0)) x2) x3) = True.
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) := (@IN a0 x2 x0) -> (real_le (real_abs (x1 x2)) x3) = True.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term44 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term64 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_le (real_abs (x0 x1)).
Definition term76 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := real_le (@sum a0 x1 (fun y0 : a0 => real_abs (x0 y0))) (real_mul (real_of_num (@CARD a0 x1)) x2).
Definition term8 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> real_le x0 x1.
Definition term12 (x0 : real) := forall y0 : real, (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0.
Definition term11 (x0 : real) (x1 : real) := (exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1)) -> real_le x0 x1.
Definition term55 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term71 (a0 : Type') := fun y0 : a0 => True.
Definition term56 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term78 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := exists y0 : real, (real_le (real_abs (@sum a0 x1 x0)) y0) /\ (real_le y0 (real_mul (real_of_num (@CARD a0 x1)) x2)).
Definition term42 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 => real_abs (x0 y0).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_abs (x1 y0)).
Definition term37 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : real) := real_le (real_abs (x0 x1)) x2.
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1) x0.
Definition term77 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := (real_le (real_abs (@sum a0 x1 x0)) (@sum a0 x1 (fun y0 : a0 => real_abs (x0 y0)))) /\ (real_le (@sum a0 x1 (fun y0 : a0 => real_abs (x0 y0))) (real_mul (real_of_num (@CARD a0 x1)) x2)).
Definition term31 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := (fun y0 : real => ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) y0)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) y0)) x2.
Definition term22 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> real_le (real_abs (@sum a0 y1 y0)) (@sum a0 y1 (fun y2 : a0 => real_abs (y0 y2)))) x0.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) (x4 : Prop) := forall y0 : Prop, ((@IN a0 x2 x0) = x4) -> (x4 -> (real_le ((fun y1 : a0 => real_abs (x1 y1)) x2) x3) = y0) -> ((@IN a0 x2 x0) -> real_le ((fun y1 : a0 => real_abs (x1 y1)) x2) x3) = (x4 -> y0).
Definition term45 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term24 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> real_le (real_abs (@sum a0 y0 x0)) (@sum a0 y0 (fun y1 : a0 => real_abs (x0 y1)))) x1.
Definition term32 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) x2)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> (real_le ((fun y2 : a0 => real_abs (x1 y2)) x2) x3) = y1) -> ((@IN a0 x2 x0) -> real_le ((fun y2 : a0 => real_abs (x1 y2)) x2) x3) = (y0 -> y1).
Definition term46 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term59 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_abs (x0 x1).
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1) x1.
Definition term84 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> real, forall y1 : real, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> real_le (real_abs (y0 y2)) y1)) -> real_le (real_abs (@sum a0 x0 y0)) (real_mul (real_of_num (@CARD a0 x0)) y1).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> real, forall y1 : real, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> real_le (y0 y2) y1)) -> real_le (@sum a0 x0 y0) (real_mul (real_of_num (@CARD a0 x0)) y1).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@FINITE a0 x0) -> real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0))).
Definition term34 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2).
Definition term5 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0) x2.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((@IN a0 x2 x0) = x4) -> (x4 -> (real_le ((fun y1 : a0 => real_abs (x1 y1)) x2) x3) = y0) -> ((@IN a0 x2 x0) -> real_le ((fun y1 : a0 => real_abs (x1 y1)) x2) x3) = (x4 -> y0)) x5.
Definition term81 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := real_le (real_abs (@sum a0 x1 x0)) (real_mul (real_of_num (@CARD a0 x1)) x2).
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0) x1.
Definition term4 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le ((fun y1 : a0 => real_abs (x1 y1)) y0) x2).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_abs (x1 y0)) x2).
Definition term7 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term41 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le ((fun y1 : a0 => real_abs (x0 y1)) y0) x2)) -> (real_le (@sum a0 x1 (fun y0 : a0 => real_abs (x0 y0))) (real_mul (real_of_num (@CARD a0 x1)) x2)) = True.
Definition term40 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) x2)) -> (real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = True.
Definition term60 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 => (fun y1 : a0 => real_abs (x0 y1)) y0.
Definition term58 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => real_abs (x0 y0)) x1.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> (real_le ((fun y2 : a0 => real_abs (x1 y2)) x2) x3) = y1) -> ((@IN a0 x2 x0) -> real_le ((fun y2 : a0 => real_abs (x1 y2)) x2) x3) = (y0 -> y1)) x4.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) := (@IN a0 x2 x0) -> real_le ((fun y0 : a0 => real_abs (x1 y0)) x2) x3.
Definition term57 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => real_abs (x0 y1)) y0) x1.
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) x0.
Definition term82 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (real_abs (x0 y0)) x2)) -> real_le (real_abs (@sum a0 x1 x0)) (real_mul (real_of_num (@CARD a0 x1)) x2).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := fun y0 : a0 => (@IN a0 y0 x0) -> real_le ((fun y1 : a0 => real_abs (x1 y1)) y0) x2.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0))).
Definition term19 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := (exists y0 : real, (real_le (real_abs (@sum a0 x1 x0)) y0) /\ (real_le y0 (real_mul (real_of_num (@CARD a0 x1)) x2))) -> real_le (real_abs (@sum a0 x1 x0)) (real_mul (real_of_num (@CARD a0 x1)) x2).
