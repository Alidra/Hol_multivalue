Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := @eq Prop ((fun y0 : real => (@sum a0 (@DELETE a0 x1 x0) x2) = y0) (@COND real (@IN a0 x0 x1) (real_sub (@sum a0 x1 x2) (x2 x0)) (@sum a0 x1 x2))).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := real_sub (@sum a0 x0 x1) (x1 x2).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and ((~ (x0 x1)) \/ (x1 = x2)).
Definition term64 (a0 : Type') (x0 : real) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) (x4 : a0 -> real) (x5 : real) := (x1 -> (fun y0 : real => (@sum a0 (@DELETE a0 x2 x3) x4) = y0) x0) /\ ((~ x1) -> (fun y0 : real => (@sum a0 (@DELETE a0 x2 x3) x4) = y0) x5).
Definition term58 := (~ False) -> False.
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term27 (x0 : Prop) := ~ (~ x0).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x0 x1) /\ (~ (x1 = x2))).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or (((x1 x2) /\ (~ (x2 = x0))) /\ (~ (x1 x2))).
Definition term69 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := (fun y0 : real => (@sum a0 (@DELETE a0 x1 x0) x2) = y0) (@sum a0 x1 x2).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (~ (@IN a0 x0 x1)).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (fun y0 : real => (@sum a0 (@DELETE a0 x0 x2) x1) = y0) (real_sub (@sum a0 x0 x1) (x1 x2)).
Definition term99 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, forall y2 : a0, (@FINITE a0 y1) -> (@sum a0 (@DELETE a0 y1 y2) y0) = (@COND real (@IN a0 y2 y1) (real_sub (@sum a0 y1 y0) (y0 y2)) (@sum a0 y1 y0)).
Definition term85 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, ((@FINITE a0 y0) /\ (@IN a0 y1 y0)) -> (@sum a0 (@DELETE a0 y0 y1) x0) = (real_sub (@sum a0 y0 x0) (x0 y1))) x1.
Definition term20 (x0 : Prop) := (~ x0) -> False.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => ((@FINITE a0 x0) /\ (@IN a0 y0 x0)) -> (@sum a0 (@DELETE a0 x0 y0) x1) = (real_sub (@sum a0 x0 x1) (x1 y0))) x2.
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (~ ((~ (x0 y0)) -> forall y1 : a0, ((x0 y1) /\ (~ (y1 = y0))) = (x0 y1))) -> False.
Definition term83 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, forall y2 : a0, ((@FINITE a0 y1) /\ (@IN a0 y2 y1)) -> (@sum a0 (@DELETE a0 y1 y2) y0) = (real_sub (@sum a0 y1 y0) (y0 y2))) x0.
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x1 x2)) \/ (x2 = x0)) /\ (x1 x2).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (~ (x0 y0)) -> forall y1 : a0, ((x0 y1) /\ (~ (y1 = y0))) = (x0 y1).
Definition term56 (x0 : Prop) := (~ x0) -> x0.
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@DELETE a0 x1 x2).
Definition term50 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (~ (x2 = x0))) /\ (~ (x1 x2)).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := @sum a0 (@DELETE a0 x0 x1) x2.
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) /\ (~ (x2 = x0))) /\ (~ (x1 x2))) \/ (((~ (x1 x2)) \/ (x2 = x0)) /\ (x1 x2)).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := and ((@IN a0 x2 x0) -> (fun y0 : real => (@sum a0 (@DELETE a0 x0 x2) x1) = y0) (real_sub (@sum a0 x0 x1) (x1 x2))).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := and ((@IN a0 x2 x0) -> (@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))).
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> (@DELETE a0 x1 x0) = x1.
Definition term89 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@IN a0 x0 x1).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (~ ((~ (x0 y0)) -> forall y1 : a0, ((x0 y1) /\ (~ (y1 = y0))) = (x0 y1))) -> False.
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x1 x2) /\ (~ (x2 = x0))) = (x1 x2)).
Definition term62 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term34 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (~ ((~ (y0 y1)) -> forall y2 : a0, ((y0 y2) /\ (~ (y2 = y1))) = (y0 y2))) -> False.
Definition term82 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := @eq Prop ((@sum a0 (@DELETE a0 x1 x0) x2) = (@COND real (@IN a0 x0 x1) (real_sub (@sum a0 x1 x2) (x2 x0)) (@sum a0 x1 x2))).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, ((@FINITE a0 x0) /\ (@IN a0 y0 x0)) -> (@sum a0 (@DELETE a0 x0 y0) x1) = (real_sub (@sum a0 x0 x1) (x1 y0)).
Definition term96 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := (@FINITE a0 x1) -> (@sum a0 (@DELETE a0 x1 x0) x2) = (@COND real (@IN a0 x0 x1) (real_sub (@sum a0 x1 x2) (x2 x0)) (@sum a0 x1 x2)).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term71 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := (~ (@IN a0 x0 x1)) -> (fun y0 : real => (@sum a0 (@DELETE a0 x1 x0) x2) = y0) (@sum a0 x1 x2).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, (@FINITE a0 x0) -> (@sum a0 (@DELETE a0 x0 y0) x1) = (@COND real (@IN a0 y0 x0) (real_sub (@sum a0 x0 x1) (x1 y0)) (@sum a0 x0 x1)).
Definition term67 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@IN a0 x0 x1) -> (fun y0 : real => (@sum a0 (@DELETE a0 x1 x0) x2) = y0) (real_sub (@sum a0 x1 x2) (x2 x0))) /\ ((~ (@IN a0 x0 x1)) -> (fun y0 : real => (@sum a0 (@DELETE a0 x1 x0) x2) = y0) (@sum a0 x1 x2)).
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))) -> False) -> (~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))) -> False.
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (((x1 x2) /\ (~ (x2 = x0))) = (x1 x2))) -> False.
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := @eq real (real_sub (@sum a0 x0 x1) (x1 x2)).
Definition term93 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> (@IN a0 x0 x1) = False.
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@IN a0 x0 x1) -> (@sum a0 (@DELETE a0 x1 x0) x2) = (real_sub (@sum a0 x1 x2) (x2 x0))) /\ ((~ (@IN a0 x0 x1)) -> (@sum a0 (@DELETE a0 x1 x0) x2) = (@sum a0 x1 x2)).
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ (~ (x1 = x2)).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@sum a0 x0 x1).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @sum a0 (@DELETE a0 x0 x1).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and (~ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) -> (fun y0 : real => (@sum a0 (@DELETE a0 x0 x2) x1) = y0) (real_sub (@sum a0 x0 x1) (x1 x2)).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ (~ (x1 = x2)).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0).
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (((~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))) -> False) -> (~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))) -> False) -> (~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))) -> False.
Definition term74 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (@IN a0 x0 (@DELETE a0 x1 x2)).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@DELETE a0 x1 x0)) = (@IN a0 y0 x1).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x1 x2) /\ (~ (x2 = x0)))) /\ (x1 x2).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) (x3 : Prop) (x4 : real) (x5 : real) := (fun y0 : real => (@sum a0 (@DELETE a0 x0 x1) x2) = y0) (@COND real x3 x4 x5).
Definition term80 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := @COND real (@IN a0 x0 x1) (real_sub (@sum a0 x1 x2) (x2 x0)) (@sum a0 x1 x2).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (~ ((~ (y0 y1)) -> forall y2 : a0, ((y0 y2) /\ (~ (y2 = y1))) = (y0 y2))) -> False) x0.
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (~ ((~ (x0 y0)) -> forall y1 : a0, ((x0 y1) /\ (~ (y1 = y0))) = (x0 y1))) -> False) x1.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (~ (x0 x1)).
Definition term72 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := (~ (@IN a0 x0 x1)) -> (@sum a0 (@DELETE a0 x1 x0) x2) = (@sum a0 x1 x2).
Definition term61 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => x0 y0) x1).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (~ (~ (x1 = x2))).
Definition term32 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (~ ((~ (y0 y1)) -> forall y2 : a0, ((y0 y2) /\ (~ (y2 = y1))) = (y0 y2))) -> False.
Definition term33 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (~ (y0 y1)) -> forall y2 : a0, ((y0 y2) /\ (~ (y2 = y1))) = (y0 y2).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := @eq real (@sum a0 (@DELETE a0 x0 x1) x2).
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) /\ (~ (x2 = x0))) /\ (~ (x1 x2))) \/ ((~ ((x1 x2) /\ (~ (x2 = x0)))) /\ (x1 x2)).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := ((@FINITE a0 x0) /\ (@IN a0 x2 x0)) -> (@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2)).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0)).
Definition term66 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := (fun y0 : real => (@sum a0 (@DELETE a0 x1 x0) x2) = y0) (@COND real (@IN a0 x0 x1) (real_sub (@sum a0 x1 x2) (x2 x0)) (@sum a0 x1 x2)).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) -> (@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2)).
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (((~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))) -> False) -> (~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))) -> False) -> ((~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))) -> False) -> (~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))) -> False.
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@DELETE a0 x1 x0)) = (@IN a0 y0 x1).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ ((~ (x1 x0)) -> forall y0 : a0, ((x1 y0) /\ (~ (y0 = x0))) = (x1 y0))) -> False.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := @eq Prop ((x0 x1) /\ (~ (x1 = x2))).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (x1 = x2).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> forall y0 : a0, (@IN a0 y0 (@DELETE a0 x1 x0)) = (@IN a0 y0 x1).
Definition term98 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, forall y1 : a0, (@FINITE a0 y0) -> (@sum a0 (@DELETE a0 y0 y1) x0) = (@COND real (@IN a0 y1 y0) (real_sub (@sum a0 y0 x0) (x0 y1)) (@sum a0 y0 x0)).
Definition term84 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, forall y1 : a0, ((@FINITE a0 y0) /\ (@IN a0 y1 y0)) -> (@sum a0 (@DELETE a0 y0 y1) x0) = (real_sub (@sum a0 y0 x0) (x0 y1)).
Definition term35 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (~ (y0 y1)) -> forall y2 : a0, ((y0 y2) /\ (~ (y2 = y1))) = (y0 y2).
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (~ (x0 y0)) -> forall y1 : a0, ((x0 y1) /\ (~ (y1 = y0))) = (x0 y1).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := fun y0 : real => (@sum a0 (@DELETE a0 x0 x1) x2) = y0.
