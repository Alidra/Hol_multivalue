Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term136 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (x2 x0) /\ (((x1 x0) = (x1 y0)) /\ (x2 y0))) x3.
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (@IN a1 (x0 y1) (@IMAGE a0 a1 x0 x1))) y1)).
Definition term183 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (@FINITE a1 (@IMAGE a0 a1 x0 x1)) -> @FINITE a0 x1.
Definition term68 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => ((x1 x0) = (x1 y0)) /\ (x2 y0).
Definition term128 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (x2 x0) /\ (((x1 x0) = (x1 y0)) /\ (x2 y0)).
Definition term172 := (~ False) -> False.
Definition term28 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term180 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (~ (forall y2 : a0, ((y0 y2) /\ (exists y3 : a0, ((y1 y2) = (y1 y3)) /\ (y0 y3))) = (y0 y2))) -> False) x0.
Definition term102 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (~ ((x1 x0) = (x1 y0))) \/ (~ (x2 y0)).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) -> @FINITE a0 x1.
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term105 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (~ (x2 x0)) \/ (~ (exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0))).
Definition term160 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0, ((x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))) \/ (((~ (x1 x2)) \/ (forall y0 : a0, (~ ((x0 x2) = (x0 y0))) \/ (~ (x1 y0)))) /\ (x1 x2))).
Definition term159 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => ((x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) /\ (~ (x1 x2))) y0) \/ (((~ (x1 x2)) \/ (forall y0 : a0, (~ ((x0 x2) = (x0 y0))) \/ (~ (x1 y0)))) /\ (x1 x2))).
Definition term146 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => ((fun y1 : a0 => (x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) y0) /\ (~ (x1 x2)).
Definition term82 (x0 : Prop) := ~ (~ x0).
Definition term107 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := ~ ((x2 x0) /\ (exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0))).
Definition term156 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => (fun y1 : a0 => ((x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) /\ (~ (x1 x2))) y0.
Definition term165 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => ((fun y1 : a0 => ((x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) /\ (~ (x1 x2))) y0) \/ (((~ (x1 x2)) \/ (forall y1 : a0, (~ ((x0 x2) = (x0 y1))) \/ (~ (x1 y1)))) /\ (x1 x2)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1 -> Prop) := forall y0 : a0 -> Prop, ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) /\ (@FINITE a1 x1)) -> @FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (@IN a1 (x0 y2) x1)) y2)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term147 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => ((x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2)).
Definition term148 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, ((x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2)).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term50 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x2) /\ (@IN a1 (x1 y1) (@IMAGE a0 a1 x1 x2))) y0) y0.
Definition term90 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, forall y2 : a0, ((y0 y2) /\ (exists y3 : a0, ((y1 y2) = (y1 y3)) /\ (y0 y3))) = (y0 y2).
Definition term119 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term75 (x0 : Prop) := (~ x0) -> False.
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term144 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : a0 => (x2 x3) /\ (((x0 x3) = (x0 y0)) /\ (x2 y0))) x1) /\ (~ (x2 x3)).
Definition term155 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := (fun y0 : a0 => ((x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))) x3.
Definition term92 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x1 x2) /\ (exists y0 : a0, ((x0 x2) = (x0 y0)) /\ (x1 y0))) = (x1 x2)).
Definition term117 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) /\ (exists y0 : a0, ((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))) \/ (((~ (x1 x2)) \/ (forall y0 : a0, (~ ((x0 x2) = (x0 y0))) \/ (~ (x1 y0)))) /\ (x1 x2)).
Definition term83 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a1 => (~ (forall y1 : a0, ((x0 y1) /\ (exists y2 : a0, ((y0 y1) = (y0 y2)) /\ (x0 y2))) = (x0 y1))) -> False.
Definition term158 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := or (exists y0 : a0, (fun y1 : a0 => ((x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) /\ (~ (x1 x2))) y0).
Definition term84 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a1 => forall y1 : a0, ((x0 y1) /\ (exists y2 : a0, ((y0 y1) = (y0 y2)) /\ (x0 y2))) = (x0 y1).
Definition term186 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) -> (@FINITE a1 (@IMAGE a0 a1 x0 y0)) = (@FINITE a0 y0).
Definition term179 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (((x0 x2) = (x0 x2)) /\ (x1 x2)) -> False.
Definition term73 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := fun y0 : a0 => ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0).
Definition term109 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := and (~ ((x2 x0) /\ (exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0)))).
Definition term141 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0, (x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))).
Definition term140 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) y0) /\ (~ (x1 x2))).
Definition term163 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : a0 => ((x2 x3) /\ (((x1 x3) = (x1 y0)) /\ (x2 y0))) /\ (~ (x2 x3))) x0) \/ (((~ (x2 x3)) \/ (forall y0 : a0, (~ ((x1 x3) = (x1 y0))) \/ (~ (x2 y0)))) /\ (x2 x3)).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x1) /\ (@IN a1 (x0 y0) (@IMAGE a0 a1 x0 x1)).
Definition term118 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term65 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := ((x1 x0) = (x1 x2)) /\ (@IN a0 x2 x3).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term135 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, ((fun y1 : a0 => (x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) y0) /\ (~ (x1 x2)).
Definition term175 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term170 (x0 : Prop) := (~ x0) -> x0.
Definition term49 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x2) /\ (@IN a1 (x1 y0) (@IMAGE a0 a1 x1 x2))) y0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a1 -> Prop, forall y2 : a0 -> Prop, ((forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ ((@IN a0 y4 y2) /\ ((y0 y3) = (y0 y4)))) -> y3 = y4) /\ (@FINITE a1 y1)) -> @FINITE a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (@IN a1 (y0 y4) y1)) y4))) x0.
Definition term45 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> a1) (x3 : a0 -> Prop) := @SETSPEC a0 x0 ((@IN a0 x1 x3) /\ (@IN a1 (x2 x1) (@IMAGE a0 a1 x2 x3))).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a1 (@IMAGE a0 a1 x0 y0).
Definition term176 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term122 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ((x1 x0) = (x1 y1)) /\ (x2 y1)) y0.
Definition term52 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (@IN a1 (x0 y2) (@IMAGE a0 a1 x0 x1))) y1) y1.
Definition term66 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ((x1 x0) = (x1 x3)) /\ (x2 x3).
Definition term115 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := or (((x1 x2) /\ (exists y0 : a0, ((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))).
Definition term150 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, ((x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))) \/ (((~ (x1 x2)) \/ (forall y0 : a0, (~ ((x0 x2) = (x0 y0))) \/ (~ (x1 y0)))) /\ (x1 x2)).
Definition term157 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, (fun y1 : a0 => ((x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) /\ (~ (x1 x2))) y0.
Definition term138 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (x2 x0) /\ (((x1 x0) = (x1 y1)) /\ (x2 y1))) y0.
Definition term123 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => ((x1 x0) = (x1 y1)) /\ (x2 y1)) y0.
Definition term101 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ((x1 x0) = (x1 y1)) /\ (x2 y1)) y0).
Definition term97 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := ~ (exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0)).
Definition term131 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, (x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2)).
Definition term142 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := and ((fun y0 : a0 => (x2 x0) /\ (((x1 x0) = (x1 y0)) /\ (x2 y0))) x3).
Definition term15 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term55 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x2) /\ (@IN a1 (x1 y1) (@IMAGE a0 a1 x1 x2))) y1)).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x2) /\ (@IN a1 (x1 y2) (@IMAGE a0 a1 x1 x2))) y1) y1)).
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term60 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a1 x0 (@IMAGE a0 a1 x1 x2).
Definition term162 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := or (((x2 x3) /\ (((x0 x3) = (x0 x1)) /\ (x2 x1))) /\ (~ (x2 x3))).
Definition term2 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> x0 -> x1) -> (x0 = x1) -> x0 -> x1.
Definition term145 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := ((x2 x3) /\ (((x0 x3) = (x0 x1)) /\ (x2 x1))) /\ (~ (x2 x3)).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : Prop) (x3 : Prop) := ((@FINITE a0 x1) = x2) -> (x2 -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = x3) -> ((@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1)) = (x2 -> x3).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := ((forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) /\ (@FINITE a1 (@IMAGE a0 a1 x0 x1))) -> @FINITE a0 x1.
Definition term58 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term57 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x2) /\ (@IN a1 (x1 y1) (@IMAGE a0 a1 x1 x2))) y1))).
Definition term56 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x2) /\ (@IN a1 (x1 y2) (@IMAGE a0 a1 x1 x2))) y1) y1))).
Definition term182 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (@IN a1 (x0 y1) (@IMAGE a0 a1 x0 x1))) y1))) -> @FINITE a0 x1.
Definition term121 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (x2 x0) /\ ((fun y1 : a0 => ((x1 x0) = (x1 y1)) /\ (x2 y1)) y0).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x1) /\ (@IN a1 (x0 y0) (@IMAGE a0 a1 x0 x1))) x2.
Definition term106 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (~ (x2 x0)) \/ (forall y0 : a0, (~ ((x1 x0) = (x1 y0))) \/ (~ (x2 y0))).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term78 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))) -> False) -> (~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))) -> False.
Definition term134 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, (fun y1 : a0 => (x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) y0) /\ (~ (x1 x2)).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) /\ (@FINITE a1 (@IMAGE a0 a1 x0 x1)).
Definition term91 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (~ (((x1 x2) /\ (exists y0 : a0, ((x0 x2) = (x0 y0)) /\ (x1 y0))) = (x1 x2))) -> False.
Definition term54 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (@IN a1 (x0 y2) (@IMAGE a0 a1 x0 x1))) y1) y1).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (@IN a1 (x0 y1) (@IMAGE a0 a1 x0 x1))) y1).
Definition term74 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0).
Definition term89 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (~ (forall y2 : a0, ((y0 y2) /\ (exists y3 : a0, ((y1 y2) = (y1 y3)) /\ (y0 y3))) = (y0 y2))) -> False.
Definition term0 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 -> x1.
Definition term103 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a0, (~ ((x1 x0) = (x1 y0))) \/ (~ (x2 y0)).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((@FINITE a0 x1) = x2) -> (x2 -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = y0) -> ((@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1)) = (x2 -> y0)) x3.
Definition term153 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, (fun y1 : a0 => ((x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) /\ (~ (x1 x2))) y0) \/ (((~ (x1 x2)) \/ (forall y0 : a0, (~ ((x0 x2) = (x0 y0))) \/ (~ (x1 y0)))) /\ (x1 x2)).
Definition term48 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x2) /\ (@IN a1 (x1 y1) (@IMAGE a0 a1 x1 x2))) y0) y0.
Definition term99 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => ((x1 x0) = (x1 y0)) /\ (x2 y0)) x3.
Definition term94 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x1 x0) = (x1 x3))) \/ (~ (x2 x3)).
Definition term129 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (x2 x0) /\ (((x1 x0) = (x1 y0)) /\ (x2 y0)).
Definition term51 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x2) /\ (@IN a1 (x1 y0) (@IMAGE a0 a1 x1 x2))) y0.
Definition term185 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = (@FINITE a0 x1).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x2) /\ (@IN a1 (x1 y0) (@IMAGE a0 a1 x1 x2))) x3).
Definition term70 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (x2 x0) /\ (exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0)).
Definition term114 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (exists y0 : a0, ((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2)).
Definition term178 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) = (x0 x2)) /\ (x1 x2).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : Prop) := ((@FINITE a0 x1) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = x2) -> ((@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1)) = ((@FINITE a0 x1) -> x2).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x2) /\ (@IN a1 (x1 x3) (@IMAGE a0 a1 x1 x2))) x3.
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term120 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (x2 x0) /\ (exists y0 : a0, (fun y1 : a0 => ((x1 x0) = (x1 y1)) /\ (x2 y1)) y0).
Definition term81 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))).
Definition term76 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))) -> False.
Definition term126 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (x2 x0) /\ (((x1 x0) = (x1 x3)) /\ (x2 x3)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @FINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : Prop) := forall y0 : Prop, ((@FINITE a0 x1) = x2) -> (x2 -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = y0) -> ((@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1)) = (x2 -> y0).
Definition term16 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE a1 (@IMAGE a0 a1 x0 y0)) x1.
Definition term161 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := or ((fun y0 : a0 => ((x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))) x3).
Definition term166 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => (((x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))) \/ (((~ (x1 x2)) \/ (forall y1 : a0, (~ ((x0 x2) = (x0 y1))) \/ (~ (x1 y1)))) /\ (x1 x2)).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := ((@FINITE a0 x1) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = True) -> ((@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1)) = ((@FINITE a0 x1) -> True).
Definition term79 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))) -> False) -> (~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))) -> False) -> (~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))) -> False.
Definition term85 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, (~ (forall y1 : a0, ((x0 y1) /\ (exists y2 : a0, ((y0 y1) = (y0 y2)) /\ (x0 y2))) = (x0 y1))) -> False.
Definition term62 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a1 (x1 x0) (@IMAGE a0 a1 x1 x2).
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (@IN a1 (x0 y1) (@IMAGE a0 a1 x0 x1))) y1.
Definition term29 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term164 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (((x2 x3) /\ (((x1 x3) = (x1 x0)) /\ (x2 x0))) /\ (~ (x2 x3))) \/ (((~ (x2 x3)) \/ (forall y0 : a0, (~ ((x1 x3) = (x1 y0))) \/ (~ (x2 y0)))) /\ (x2 x3)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((@FINITE a0 x1) = y0) -> (y0 -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = y1) -> ((@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1)) = (y0 -> y1).
Definition term17 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term173 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (~ ((x0 x1) = (x0 x1))) -> (x0 x1) = (x0 x1).
Definition term187 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a1 -> Prop, forall y1 : a0 -> Prop, ((forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((x0 y2) = (x0 y3)))) -> y2 = y3) /\ (@FINITE a1 y0)) -> @FINITE a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (@IN a1 (x0 y3) y0)) y3)).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : Prop) := ((@FINITE a0 x1) = (@FINITE a0 x1)) -> ((@FINITE a0 x1) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = x2) -> ((@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1)) = ((@FINITE a0 x1) -> x2).
Definition term124 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @eq Prop ((x2 x0) /\ (exists y0 : a0, (fun y1 : a0 => ((x1 x0) = (x1 y1)) /\ (x2 y1)) y0)).
Definition term71 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @eq Prop ((x2 x0) /\ (exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0))).
Definition term177 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (((x1 x0) = (x1 x3)) /\ (x2 x3)) -> False.
Definition term184 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := ((@FINITE a1 (@IMAGE a0 a1 x0 x1)) -> @FINITE a0 x1) /\ ((@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1)).
Definition term87 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (~ (forall y2 : a0, ((y0 y2) /\ (exists y3 : a0, ((y1 y2) = (y1 y3)) /\ (y0 y3))) = (y0 y2))) -> False.
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = True.
Definition term143 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := and ((x2 x0) /\ (((x1 x0) = (x1 x3)) /\ (x2 x3))).
Definition term113 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := and ((x2 x0) /\ (exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0))).
Definition term69 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((x1 y0) = (x1 y1)))) -> y0 = y1.
Definition term100 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ~ ((fun y0 : a0 => ((x1 x0) = (x1 y0)) /\ (x2 y0)) x3).
Definition term154 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, ((fun y1 : a0 => ((x1 x2) /\ (((x0 x2) = (x0 y1)) /\ (x1 y1))) /\ (~ (x1 x2))) y0) \/ (((~ (x1 x2)) \/ (forall y1 : a0, (~ ((x0 x2) = (x0 y1))) \/ (~ (x1 y1)))) /\ (x1 x2)).
Definition term168 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (~ ((x1 x0) = (x1 y0))) \/ (~ (x2 y0))) x3.
Definition term130 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := and (exists y0 : a0, (x2 x0) /\ (((x1 x0) = (x1 y0)) /\ (x2 y0))).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := ((@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (@IN a1 (x0 y1) (@IMAGE a0 a1 x0 x1))) y1))) = (@FINITE a0 x1)) -> (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (@IN a1 (x0 y1) (@IMAGE a0 a1 x0 x1))) y1))) -> @FINITE a0 x1.
Definition term64 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) := and ((x1 x0) = (x1 x2)).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term181 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (~ (forall y1 : a0, ((x0 y1) /\ (exists y2 : a0, ((y0 y1) = (y0 y2)) /\ (x0 y2))) = (x0 y1))) -> False) x1.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : a0 -> Prop, ((forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((x0 y2) = (x0 y3)))) -> y2 = y3) /\ (@FINITE a1 y0)) -> @FINITE a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (@IN a1 (x0 y3) y0)) y3))) x1.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) /\ (@FINITE a1 x1)) -> @FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (@IN a1 (x0 y2) x1)) y2))) x2.
Definition term125 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (x2 x0) /\ ((fun y0 : a0 => ((x1 x0) = (x1 y0)) /\ (x2 y0)) x3).
Definition term127 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (x2 x0) /\ ((fun y1 : a0 => ((x1 x0) = (x1 y1)) /\ (x2 y1)) y0).
Definition term116 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) /\ (exists y0 : a0, ((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))) \/ ((~ ((x1 x2) /\ (exists y0 : a0, ((x0 x2) = (x0 y0)) /\ (x1 y0)))) /\ (x1 x2)).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a1 -> Prop) := ((forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((x1 y0) = (x1 y1)))) -> y0 = y1) /\ (@FINITE a1 x2)) -> @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (@IN a1 (x1 y1) x2)) y1)).
Definition term88 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : a0, ((y0 y2) /\ (exists y3 : a0, ((y1 y2) = (y1 y3)) /\ (y0 y3))) = (y0 y2).
Definition term63 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term61 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := ((forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) /\ (@FINITE a1 (@IMAGE a0 a1 x0 x1))) -> @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (@IN a1 (x0 y1) (@IMAGE a0 a1 x0 x1))) y1)).
Definition term80 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))) -> False) -> (~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))) -> False) -> ((~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))) -> False) -> (~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0))) -> False.
Definition term137 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (x2 x0) /\ (((x1 x0) = (x1 y1)) /\ (x2 y1))) y0.
Definition term38 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (@IN a1 (x0 y2) (@IMAGE a0 a1 x0 x1))) y2))) = (@IN a0 y0 x1).
Definition term1 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> x0 -> x1) -> x0 -> x1.
Definition term46 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x2) /\ (@IN a1 (x1 y0) (@IMAGE a0 a1 x1 x2))) x3) x3.
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term111 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x1 x2) /\ (exists y0 : a0, ((x0 x2) = (x0 y0)) /\ (x1 y0)))) /\ (x1 x2).
Definition term67 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => ((x1 x0) = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a1 (@IMAGE a0 a1 y0 y1)) x0.
Definition term139 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := and (exists y0 : a0, (fun y1 : a0 => (x2 x0) /\ (((x1 x0) = (x1 y1)) /\ (x2 y1))) y0).
Definition term98 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => ((x1 x0) = (x1 y1)) /\ (x2 y1)) y0).
Definition term72 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (@IN a1 (x0 y2) (@IMAGE a0 a1 x0 x1))) y2))) = (@IN a0 y0 x1).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> True.
Definition term167 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, (((x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))) \/ (((~ (x1 x2)) \/ (forall y1 : a0, (~ ((x0 x2) = (x0 y1))) \/ (~ (x1 y1)))) /\ (x1 x2)).
Definition term43 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (@IN a0 x0 x2) /\ (@IN a1 (x1 x0) (@IMAGE a0 a1 x1 x2)).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@FINITE a0 x1) = y0) -> (y0 -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = y1) -> ((@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1)) = (y0 -> y1)) x2.
Definition term169 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term77 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ((x1 y0) /\ (exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1))) = (x1 y0)).
Definition term86 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : a0, ((x0 y1) /\ (exists y2 : a0, ((y0 y1) = (y0 y2)) /\ (x0 y2))) = (x0 y1).
Definition term174 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := ~ ((x0 x1) = (x0 x1)).
Definition term112 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x1 x2)) \/ (forall y0 : a0, (~ ((x0 x2) = (x0 y0))) \/ (~ (x1 y0)))) /\ (x1 x2).
Definition term149 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := or (exists y0 : a0, ((x1 x2) /\ (((x0 x2) = (x0 y0)) /\ (x1 y0))) /\ (~ (x1 x2))).
Definition term93 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ~ (((x1 x0) = (x1 x3)) /\ (x2 x3)).
Definition term110 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := and ((~ (x2 x0)) \/ (forall y0 : a0, (~ ((x1 x0) = (x1 y0))) \/ (~ (x2 y0)))).
