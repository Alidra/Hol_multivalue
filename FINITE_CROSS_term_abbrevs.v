Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : Prop) := (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = x2) -> (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> x2).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a1 -> Prop => ((@FINITE a0 x0) /\ (@FINITE a1 y0)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 y0).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, ((@FINITE a0 x0) /\ (@FINITE a1 y0)) -> @FINITE (prod a0 a1) (@GSPEC (prod a0 a1) (fun y1 : prod a0 a1 => exists y2 : a0, exists y3 : a1, @SETSPEC (prod a0 a1) y1 ((@IN a0 y2 x0) /\ (@IN a1 y3 y0)) (@pair a0 a1 y2 y3))).
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, ((@FINITE a0 x0) /\ (@FINITE a1 y0)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 y0).
Definition term33 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (@FINITE a0 x0) /\ (@FINITE a1 x1).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := ((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = True.
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := ((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> (@FINITE (prod a0 a1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 x1)) (@pair a0 a1 y1 y2)))) = True.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@CROSS a0 a1 x0 y0) = (@GSPEC (prod a1 a0) (fun y1 : prod a1 a0 => exists y2 : a1, exists y3 : a0, @SETSPEC (prod a1 a0) y1 ((@IN a1 y2 x0) /\ (@IN a0 y3 y0)) (@pair a1 a0 y2 y3)))) x1.
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (((@FINITE a0 x0) /\ (@FINITE a1 x1)) = x2) -> (x2 -> (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = y0) -> (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = (x2 -> y0)) x3.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, ((@FINITE a0 y0) /\ (@FINITE a1 y1)) -> @FINITE (prod a0 a1) (@GSPEC (prod a0 a1) (fun y2 : prod a0 a1 => exists y3 : a0, exists y4 : a1, @SETSPEC (prod a0 a1) y2 ((@IN a0 y3 y0) /\ (@IN a1 y4 y1)) (@pair a0 a1 y3 y4)))) x0.
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : Prop) := forall y0 : Prop, (((@FINITE a0 x0) /\ (@FINITE a1 x1)) = x2) -> (x2 -> (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = y0) -> (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = (x2 -> y0).
Definition term11 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term29 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := forall y0 : Prop, forall y1 : Prop, (((@FINITE a0 x0) /\ (@FINITE a1 x1)) = y0) -> (y0 -> (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = y1) -> (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = (y0 -> y1).
Definition term12 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term35 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, ((@FINITE a0 y0) /\ (@FINITE a1 y1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 y0 y1).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = True) -> (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> True).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : a0 -> Prop, (@CROSS a0 a1 x0 y0) = (@GSPEC (prod a1 a0) (fun y1 : prod a1 a0 => exists y2 : a1, exists y3 : a0, @SETSPEC (prod a1 a0) y1 ((@IN a1 y2 x0) /\ (@IN a0 y3 y0)) (@pair a1 a0 y2 y3))).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (fun y0 : a1 -> Prop => ((@FINITE a0 x0) /\ (@FINITE a1 y0)) -> @FINITE (prod a0 a1) (@GSPEC (prod a0 a1) (fun y1 : prod a0 a1 => exists y2 : a0, exists y3 : a1, @SETSPEC (prod a0 a1) y1 ((@IN a0 y2 x0) /\ (@IN a1 y3 y0)) (@pair a0 a1 y2 y3)))) x1.
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := @GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 x1)) (@pair a0 a1 y1 y2)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := @GSPEC (prod a1 a0) (fun y0 : prod a1 a0 => exists y1 : a1, exists y2 : a0, @SETSPEC (prod a1 a0) y0 ((@IN a1 y1 x0) /\ (@IN a0 y2 x1)) (@pair a1 a0 y1 y2)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : Prop) (x3 : Prop) := (((@FINITE a0 x0) /\ (@FINITE a1 x1)) = x2) -> (x2 -> (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = x3) -> (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = (x2 -> x3).
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := ((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> True.
Definition term34 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, ((@FINITE a0 y0) /\ (@FINITE a1 y1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 y0 y1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : a0 -> Prop, (@CROSS a0 a1 y0 y1) = (@GSPEC (prod a1 a0) (fun y2 : prod a1 a0 => exists y3 : a1, exists y4 : a0, @SETSPEC (prod a1 a0) y2 ((@IN a1 y3 y0) /\ (@IN a0 y4 y1)) (@pair a1 a0 y3 y4)))) x0.
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := ((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : Prop) := (((@FINITE a0 x0) /\ (@FINITE a1 x1)) = ((@FINITE a0 x0) /\ (@FINITE a1 x1))) -> (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = x2) -> (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> x2).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := ((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> @FINITE (prod a0 a1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 x1)) (@pair a0 a1 y1 y2))).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@FINITE a0 x0) /\ (@FINITE a1 x1)) = y0) -> (y0 -> (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = y1) -> (((@FINITE a0 x0) /\ (@FINITE a1 x1)) -> @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1)) = (y0 -> y1)) x2.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := @FINITE (prod a0 a1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 x1)) (@pair a0 a1 y1 y2))).
Definition term31 (a0 : Type') := forall y0 : a0 -> Prop, True.
