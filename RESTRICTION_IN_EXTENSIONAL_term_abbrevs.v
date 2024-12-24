Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term58 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, @IN (a0 -> a1) (@RESTRICTION a0 a1 y0 y1) (@EXTENSIONAL a0 a1 y0).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, (~ (@IN a0 y0 x0)) -> (@RESTRICTION a0 a1 x0 x1 y0) = (@ARB a1).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, (~ (@IN a0 y0 x0)) -> (x1 y0) = (@ARB a1).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : a1) := (fun y0 : a1 => forall y1 : a1, ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = y0) -> ((~ x3) -> (@ARB a1) = y1) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 x3 y0 y1)) x4.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, (@RESTRICTION a0 a1 x0 y0 y1) = (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1))) x1.
Definition term52 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (@RESTRICTION a0 a1 x0 x1 y0) = (@COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1))) x2.
Definition term51 (a0 : Type') := forall y0 : a0, True.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : a0, (@RESTRICTION a0 a1 y0 y1 y2) = (@COND a1 (@IN a0 y2 y0) (y1 y2) (@ARB a1))) x0.
Definition term26 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term62 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term57 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, x0.
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : a1) := forall y0 : a1, ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((~ x3) -> (@ARB a1) = y0) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 x3 x4 y0).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : a1) (x5 : a1) := (fun y0 : a1 => ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((~ x3) -> (@ARB a1) = y0) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 x3 x4 y0)) x5.
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 x1).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (@IN a0 x2 x0)) = y0) -> (y0 -> ((@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = y1) -> ((~ (@IN a0 x2 x0)) -> (@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = (y0 -> y1)) x3.
Definition term47 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (~ (@IN a0 x2 x0)) -> (@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := ((~ False) -> (@ARB a1) = (@ARB a1)) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 False (x1 x2) (@ARB a1)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : Prop) := ((~ (@IN a0 x2 x0)) = x3) -> (x3 -> ((@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = x4) -> ((~ (@IN a0 x2 x0)) -> (@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = (x3 -> x4).
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) (x4 : a1) := ((@IN a0 x2 x0) = False) -> (False -> (x1 x2) = x3) -> ((~ False) -> (@ARB a1) = x4) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 False x3 x4).
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> True.
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> (@IN a0 x0 x1) = False.
Definition term50 (a0 : Type') := fun y0 : a0 => True.
Definition term55 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, @IN (a0 -> a1) (@RESTRICTION a0 a1 x0 y0) (@EXTENSIONAL a0 a1 x0).
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a1 => @IN (a0 -> a1) (@RESTRICTION a0 a1 x0 y0) (@EXTENSIONAL a0 a1 x0).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @eq a1 (@RESTRICTION a0 a1 x0 x1 x2).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, (@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 x0)) = (forall y1 : a0, (~ (@IN a0 y1 x0)) -> (y0 y1) = (@ARB a1)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@IN (a0 -> a1) y1 (@EXTENSIONAL a0 a1 y0)) = (forall y2 : a0, (~ (@IN a0 y2 y0)) -> (y1 y2) = (@ARB a1))) x0.
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) := forall y0 : Prop, ((~ (@IN a0 x2 x0)) = x3) -> (x3 -> ((@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = y0) -> ((~ (@IN a0 x2 x0)) -> (@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = (x3 -> y0).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term54 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => True.
Definition term59 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : a1, forall y2 : a1, ((@IN a0 x2 x0) = y0) -> (y0 -> (x1 x2) = y1) -> ((~ y0) -> (@ARB a1) = y2) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 y0 y1 y2)) x3.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := forall y0 : Prop, forall y1 : a1, forall y2 : a1, ((@IN a0 x2 x0) = y0) -> (y0 -> (x1 x2) = y1) -> ((~ y0) -> (@ARB a1) = y2) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 y0 y1 y2).
Definition term28 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, ((~ (@IN a0 x2 x0)) = y0) -> (y0 -> ((@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = y1) -> ((~ (@IN a0 x2 x0)) -> (@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = (y0 -> y1).
Definition term15 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term60 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, @IN (a0 -> a1) (@RESTRICTION a0 a1 y0 y1) (@EXTENSIONAL a0 a1 y0).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) := ((~ False) -> (@ARB a1) = x3) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 False (x1 x2) x3).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) := (False -> (x1 x2) = (x1 x2)) -> ((~ False) -> (@ARB a1) = x3) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 False (x1 x2) x3).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((~ (@IN a0 x2 x0)) = x3) -> (x3 -> ((@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = y0) -> ((~ (@IN a0 x2 x0)) -> (@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = (x3 -> y0)) x4.
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((~ (@IN a0 x1 x2)) -> ((@RESTRICTION a0 a1 x2 x0 x1) = (@ARB a1)) = x3) -> ((~ (@IN a0 x1 x2)) -> (@RESTRICTION a0 a1 x2 x0 x1) = (@ARB a1)) = ((~ (@IN a0 x1 x2)) -> x3).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := False -> (x0 x1) = (x0 x1).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @IN (a0 -> a1) (@RESTRICTION a0 a1 x1 x0) (@EXTENSIONAL a0 a1 x1).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : a1) (x5 : a1) := ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((~ x3) -> (@ARB a1) = x5) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 x3 x4 x5).
Definition term43 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @COND a1 False (x0 x1) (@ARB a1).
Definition term27 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) := forall y0 : a1, forall y1 : a1, ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = y0) -> ((~ x3) -> (@ARB a1) = y1) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 x3 y0 y1).
Definition term45 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (~ (@IN a0 x2 x0)) -> ((@RESTRICTION a0 a1 x0 x1 x2) = (@ARB a1)) = True.
Definition term41 (a0 : Type') := (~ False) -> (@ARB a0) = (@ARB a0).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) (x4 : a1) := (False -> (x1 x2) = x3) -> ((~ False) -> (@ARB a1) = x4) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 False x3 x4).
Definition term49 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := fun y0 : a0 => (~ (@IN a0 y0 x0)) -> (@RESTRICTION a0 a1 x0 x1 y0) = (@ARB a1).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((~ (@IN a0 x1 x2)) = (~ (@IN a0 x1 x2))) -> ((~ (@IN a0 x1 x2)) -> ((@RESTRICTION a0 a1 x2 x0 x1) = (@ARB a1)) = x3) -> ((~ (@IN a0 x1 x2)) -> (@RESTRICTION a0 a1 x2 x0 x1) = (@ARB a1)) = ((~ (@IN a0 x1 x2)) -> x3).
Definition term46 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) := ((~ (@IN a0 x1 x2)) -> ((@RESTRICTION a0 a1 x2 x0 x1) = (@ARB a1)) = True) -> ((~ (@IN a0 x1 x2)) -> (@RESTRICTION a0 a1 x2 x0 x1) = (@ARB a1)) = ((~ (@IN a0 x1 x2)) -> True).
Definition term25 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : a0, (@RESTRICTION a0 a1 x0 y0 y1) = (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1)).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 x0)) = (forall y1 : a0, (~ (@IN a0 y1 x0)) -> (y0 y1) = (@ARB a1))) x1.
Definition term61 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term56 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, True.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, (@RESTRICTION a0 a1 x0 x1 y0) = (@COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1)).
