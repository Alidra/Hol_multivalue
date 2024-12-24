Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) (x2 : a1 -> Prop) := @SUBSET a1 (@support a1 a0 x0 x1 x2) x2.
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) (x2 : a1) (x3 : a1 -> Prop) (x4 : Prop) (x5 : Prop) := ((@IN a1 x2 (@support a1 a0 x0 x1 x3)) = x4) -> (x4 -> (@IN a1 x2 x3) = x5) -> ((@IN a1 x2 (@support a1 a0 x0 x1 x3)) -> @IN a1 x2 x3) = (x4 -> x5).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) := (((@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3)))) -> (@IN a1 x2 x0) = True) -> ((@IN a1 x2 (@support a1 a0 x3 x1 x0)) -> @IN a1 x2 x0) = (((@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3)))) -> True).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) := (@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3))).
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term45 (a0 : Type') (a1 : Type') := forall y0 : type1400 a0, forall y1 : a1 -> a0, forall y2 : a1 -> Prop, @SUBSET a1 (@support a1 a0 y0 y1 y2) y2.
Definition term31 (a0 : Type') := forall y0 : a0, True.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := (fun y0 : type1400 a0 => forall y1 : a1 -> a0, forall y2 : a1, forall y3 : a1 -> Prop, (@IN a1 y2 (@support a1 a0 y0 y1 y3)) = ((@IN a1 y2 y3) /\ (~ ((y1 y2) = (@neutral a0 y0))))) x0.
Definition term47 (a0 : Type') (x0 : Prop) := forall y0 : type1400 a0, x0.
Definition term42 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a1 -> a0, x0.
Definition term37 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term40 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := forall y0 : a1 -> a0, forall y1 : a1 -> Prop, @SUBSET a1 (@support a1 a0 x0 y0 y1) y1.
Definition term25 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : type1400 a0) (x2 : a1) (x3 : a1 -> Prop) := ((@IN a1 x2 x3) /\ (~ ((x0 x2) = (@neutral a0 x1)))) -> (@IN a1 x2 x3) = True.
Definition term28 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) := ((@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3)))) -> True.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : type1400 a0) (x3 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@IN a1 x1 (@support a1 a0 x2 x0 y0)) = ((@IN a1 x1 y0) /\ (~ ((x0 x1) = (@neutral a0 x2))))) x3.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : type1400 a0) (x2 : a1) := (fun y0 : a1 => forall y1 : a1 -> Prop, (@IN a1 y0 (@support a1 a0 x1 x0 y1)) = ((@IN a1 y0 y1) /\ (~ ((x0 y0) = (@neutral a0 x1))))) x2.
Definition term23 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) (x4 : Prop) := ((@IN a1 x2 (@support a1 a0 x3 x1 x0)) = ((@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3))))) -> (((@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3)))) -> (@IN a1 x2 x0) = x4) -> ((@IN a1 x2 (@support a1 a0 x3 x1 x0)) -> @IN a1 x2 x0) = (((@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3)))) -> x4).
Definition term15 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term43 (a0 : Type') (a1 : Type') := fun y0 : type1400 a0 => forall y1 : a1 -> a0, forall y2 : a1 -> Prop, @SUBSET a1 (@support a1 a0 y0 y1 y2) y2.
Definition term30 (a0 : Type') := fun y0 : a0 => True.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : type1400 a0) := forall y0 : a1, forall y1 : a1 -> Prop, (@IN a1 y0 (@support a1 a0 x1 x0 y1)) = ((@IN a1 y0 y1) /\ (~ ((x0 y0) = (@neutral a0 x1)))).
Definition term35 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) := forall y0 : a1 -> Prop, @SUBSET a1 (@support a1 a0 x0 x1 y0) y0.
Definition term38 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := fun y0 : a1 -> a0 => forall y1 : a1 -> Prop, @SUBSET a1 (@support a1 a0 x0 y0 y1) y1.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1400 a0) (x2 : a1 -> a0) (x3 : a1 -> Prop) := @IN a1 x0 (@support a1 a0 x1 x2 x3).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) = (forall y2 : a0, (@IN a0 y2 y0) -> @IN a0 y2 y1)) x0.
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) (x2 : a1 -> Prop) := fun y0 : a1 => (@IN a1 y0 (@support a1 a0 x0 x1 x2)) -> @IN a1 y0 x2.
Definition term44 (a0 : Type') := fun y0 : type1400 a0 => True.
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) (x2 : a1) (x3 : a1 -> Prop) (x4 : Prop) := forall y0 : Prop, ((@IN a1 x2 (@support a1 a0 x0 x1 x3)) = x4) -> (x4 -> (@IN a1 x2 x3) = y0) -> ((@IN a1 x2 (@support a1 a0 x0 x1 x3)) -> @IN a1 x2 x3) = (x4 -> y0).
Definition term16 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : type1400 a0) := forall y0 : a1 -> Prop, (@IN a1 x1 (@support a1 a0 x2 x0 y0)) = ((@IN a1 x1 y0) /\ (~ ((x0 x1) = (@neutral a0 x2)))).
Definition term34 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) (x2 : a1) (x3 : a1 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((@IN a1 x2 (@support a1 a0 x0 x1 x3)) = y0) -> (y0 -> (@IN a1 x2 x3) = y1) -> ((@IN a1 x2 (@support a1 a0 x0 x1 x3)) -> @IN a1 x2 x3) = (y0 -> y1).
Definition term17 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) (x2 : a1) (x3 : a1 -> Prop) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((@IN a1 x2 (@support a1 a0 x0 x1 x3)) = x4) -> (x4 -> (@IN a1 x2 x3) = y0) -> ((@IN a1 x2 (@support a1 a0 x0 x1 x3)) -> @IN a1 x2 x3) = (x4 -> y0)) x5.
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) (x2 : a1 -> Prop) := forall y0 : a1, (@IN a1 y0 (@support a1 a0 x0 x1 x2)) -> @IN a1 y0 x2.
Definition term39 (a0 : Type') (a1 : Type') := fun y0 : a1 -> a0 => True.
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) := (fun y0 : a1 -> a0 => forall y1 : a1, forall y2 : a1 -> Prop, (@IN a1 y1 (@support a1 a0 x0 y0 y2)) = ((@IN a1 y1 y2) /\ (~ ((y0 y1) = (@neutral a0 x0))))) x1.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := forall y0 : a1 -> a0, forall y1 : a1, forall y2 : a1 -> Prop, (@IN a1 y1 (@support a1 a0 x0 y0 y2)) = ((@IN a1 y1 y2) /\ (~ ((y0 y1) = (@neutral a0 x0)))).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0)) x1.
Definition term19 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) (x2 : a1) (x3 : a1 -> Prop) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a1 x2 (@support a1 a0 x0 x1 x3)) = y0) -> (y0 -> (@IN a1 x2 x3) = y1) -> ((@IN a1 x2 (@support a1 a0 x0 x1 x3)) -> @IN a1 x2 x3) = (y0 -> y1)) x4.
Definition term33 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) := fun y0 : a1 -> Prop => @SUBSET a1 (@support a1 a0 x0 x1 y0) y0.
Definition term24 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) (x4 : Prop) := (((@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3)))) -> (@IN a1 x2 x0) = x4) -> ((@IN a1 x2 (@support a1 a0 x3 x1 x0)) -> @IN a1 x2 x0) = (((@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3)))) -> x4).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) (x2 : a1) (x3 : a1 -> Prop) := (@IN a1 x2 (@support a1 a0 x0 x1 x3)) -> @IN a1 x2 x3.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0).
Definition term46 (a0 : Type') := forall y0 : type1400 a0, True.
Definition term41 (a0 : Type') (a1 : Type') := forall y0 : a1 -> a0, True.
Definition term36 (a0 : Type') := forall y0 : a0 -> Prop, True.
