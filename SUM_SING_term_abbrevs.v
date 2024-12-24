Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term5 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> real, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@sum a0 (@INSERT a0 y0 y2) y1) = (@COND real (@IN a0 y0 y2) (@sum a0 y2 y1) (real_add (y1 y0) (@sum a0 y2 y1))).
Definition term16 := real_of_num (NUMERAL 0).
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : real) (x3 : real) := (False -> (@sum a0 (@EMPTY a0) x1) = x2) -> ((~ False) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = x3) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real False x2 x3).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : real) (x3 : real) := ((@IN a0 x0 (@EMPTY a0)) = False) -> (False -> (@sum a0 (@EMPTY a0) x1) = x2) -> ((~ False) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = x3) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real False x2 x3).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : Prop) (x3 : real) := forall y0 : real, ((@IN a0 x0 (@EMPTY a0)) = x2) -> (x2 -> (@sum a0 (@EMPTY a0) x1) = x3) -> ((~ x2) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = y0) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real x2 x3 y0).
Definition term49 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : real) := ((~ False) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = x2) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real False (real_of_num (NUMERAL 0)) x2).
Definition term44 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @eq real (x0 x1).
Definition term48 (a0 : Type') := forall y0 : a0, True.
Definition term21 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term54 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> real, x0.
Definition term1 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : Prop) := forall y0 : real, forall y1 : real, ((@IN a0 x0 (@EMPTY a0)) = x2) -> (x2 -> (@sum a0 (@EMPTY a0) x1) = y0) -> ((~ x2) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = y1) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real x2 y0 y1).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@sum a0 (@INSERT a0 x0 y1) y0) = (@COND real (@IN a0 x0 y1) (@sum a0 y1 y0) (real_add (y0 x0) (@sum a0 y1 y0)))) x1.
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := (@FINITE a0 x1) -> (@sum a0 (@INSERT a0 x0 x1) x2) = (@COND real (@IN a0 x0 x1) (@sum a0 x1 x2) (real_add (x2 x0) (@sum a0 x1 x2))).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := @COND real (@IN a0 x0 x1) (@sum a0 x1 x2) (real_add (x2 x0) (@sum a0 x1 x2)).
Definition term50 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0, (@sum a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (y0 y1).
Definition term40 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (~ False) -> (real_add (x0 x1) (@sum a0 (@EMPTY a0) x0)) = (x0 x1).
Definition term35 (a0 : Type') (x0 : a0 -> real) := False -> (@sum a0 (@EMPTY a0) x0) = (real_of_num (NUMERAL 0)).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := real_add (x1 x0) (@sum a0 (@EMPTY a0) x1).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@sum a0 (@INSERT a0 x0 y0) x1) = (@COND real (@IN a0 x0 y0) (@sum a0 y0 x1) (real_add (x1 x0) (@sum a0 y0 x1))).
Definition term15 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => (@sum a0 (@EMPTY a0) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term46 (a0 : Type') := fun y0 : a0 => True.
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : Prop) (x3 : real) (x4 : real) := (fun y0 : real => ((@IN a0 x0 (@EMPTY a0)) = x2) -> (x2 -> (@sum a0 (@EMPTY a0) x1) = x3) -> ((~ x2) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = y0) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real x2 x3 y0)) x4.
Definition term43 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := @eq real (@sum a0 (@INSERT a0 x0 (@EMPTY a0)) x1).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : real) := (False -> (@sum a0 (@EMPTY a0) x1) = (real_of_num (NUMERAL 0))) -> ((~ False) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = x2) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real False (real_of_num (NUMERAL 0)) x2).
Definition term38 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_add (x0 x1).
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := @sum a0 (@INSERT a0 x0 (@EMPTY a0)) x1.
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@sum a0 (@INSERT a0 x0 y0) x1) = (@COND real (@IN a0 x0 y0) (@sum a0 y0 x1) (real_add (x1 x0) (@sum a0 y0 x1)))) x2.
Definition term51 (a0 : Type') := fun y0 : a0 -> real => True.
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : Prop) (x3 : real) (x4 : real) := ((@IN a0 x0 (@EMPTY a0)) = x2) -> (x2 -> (@sum a0 (@EMPTY a0) x1) = x3) -> ((~ x2) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = x4) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real x2 x3 x4).
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := forall y0 : Prop, forall y1 : real, forall y2 : real, ((@IN a0 x0 (@EMPTY a0)) = y0) -> (y0 -> (@sum a0 (@EMPTY a0) x1) = y1) -> ((~ y0) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = y2) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real y0 y1 y2).
Definition term24 (x0 : Prop) (x1 : real) (x2 : real) := forall y0 : Prop, forall y1 : real, forall y2 : real, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND real x0 x1 x2) = (@COND real y0 y1 y2).
Definition term23 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term7 (a0 : Type') (x0 : a0) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@sum a0 (@INSERT a0 x0 y1) y0) = (@COND real (@IN a0 x0 y1) (@sum a0 y1 y0) (real_add (y0 x0) (@sum a0 y1 y0))).
Definition term45 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 => (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0).
Definition term39 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_add (x0 x1) (real_of_num (NUMERAL 0)).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : Prop) (x3 : real) := (fun y0 : real => forall y1 : real, ((@IN a0 x0 (@EMPTY a0)) = x2) -> (x2 -> (@sum a0 (@EMPTY a0) x1) = y0) -> ((~ x2) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = y1) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real x2 y0 y1)) x3.
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := @COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)).
Definition term14 (a0 : Type') := forall y0 : a0 -> real, (@sum a0 (@EMPTY a0) y0) = (real_of_num (NUMERAL 0)).
Definition term42 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @COND real False (real_of_num (NUMERAL 0)) (x0 x1).
Definition term47 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0, (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0).
Definition term22 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term41 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := ((~ False) -> (real_add (x0 x1) (@sum a0 (@EMPTY a0) x0)) = (x0 x1)) -> (@COND real (@IN a0 x1 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x0) (real_add (x0 x1) (@sum a0 (@EMPTY a0) x0))) = (@COND real False (real_of_num (NUMERAL 0)) (x0 x1)).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := (@FINITE a0 (@EMPTY a0)) -> (@sum a0 (@INSERT a0 x0 (@EMPTY a0)) x1) = (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))).
Definition term4 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0 -> real) (x2 : Prop) := (fun y0 : Prop => forall y1 : real, forall y2 : real, ((@IN a0 x0 (@EMPTY a0)) = y0) -> (y0 -> (@sum a0 (@EMPTY a0) x1) = y1) -> ((~ y0) -> (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1)) = y2) -> (@COND real (@IN a0 x0 (@EMPTY a0)) (@sum a0 (@EMPTY a0) x1) (real_add (x1 x0) (@sum a0 (@EMPTY a0) x1))) = (@COND real y0 y1 y2)) x2.
Definition term0 (x0 : real) := (fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0) x0.
Definition term20 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term6 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> real, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@sum a0 (@INSERT a0 y0 y2) y1) = (@COND real (@IN a0 y0 y2) (@sum a0 y2 y1) (real_add (y1 y0) (@sum a0 y2 y1)))) x0.
Definition term52 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0, (@sum a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (y0 y1).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := @sum a0 (@INSERT a0 x0 x1) x2.
Definition term2 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term53 (a0 : Type') := forall y0 : a0 -> real, True.
