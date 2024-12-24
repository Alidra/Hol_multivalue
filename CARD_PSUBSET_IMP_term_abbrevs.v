Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) -> @SUBSET a0 x0 x1.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => ~ ((@CARD a0 y0) = (@CARD a0 x0))) x1).
Definition term42 := (~ False) -> False.
Definition term22 (x0 : Prop) := ~ (~ x0).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@SUBSET a0 x0 y0) /\ (~ ((@CARD a0 x0) = (@CARD a0 y0)))) -> (@SUBSET a0 x0 y0) /\ (~ (x0 = y0)).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (x0 = x1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ (~ (x0 = x1)).
Definition term15 (x0 : Prop) := (~ x0) -> False.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@PSUBSET a0 x0 y0) = ((@SUBSET a0 x0 y0) /\ (~ (x0 = y0))).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@PSUBSET a0 x0 y0) = ((@SUBSET a0 x0 y0) /\ (~ (x0 = y0)))) x1.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@CARD a0 x0) = (@CARD a0 x1)).
Definition term17 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1))).
Definition term40 (x0 : Prop) := (~ x0) -> x0.
Definition term12 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@SUBSET a0 x0 x1) /\ (~ (x0 = x1))).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ (@SUBSET a0 x0 x1)).
Definition term18 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) := ~ ((@CARD a0 x0) = (@CARD a0 x0)).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (~ (~ (x0 = x1))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@PSUBSET a0 y0 y1) = ((@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) x0.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ~ ((@CARD a0 y0) = (@CARD a0 x0)).
Definition term21 (a0 : Type') := ~ (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))).
Definition term16 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@SUBSET a0 x0 x1) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1)))) -> @PSUBSET a0 x0 x1.
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ~ ((@CARD a0 y0) = (@CARD a0 x0))) x1.
Definition term19 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) := (~ ((@CARD a0 x0) = (@CARD a0 x0))) -> (@CARD a0 x0) = (@CARD a0 x0).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@SUBSET a0 x0 x1) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term14 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)).
Definition term13 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (@SUBSET a0 x0 x1).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@SUBSET a0 x0 x1) /\ (~ (x0 = x1)))) -> False.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@SUBSET a0 x0 x1) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1)))) -> (@SUBSET a0 x0 x1) /\ (~ (x0 = x1)).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (x0 = x1).
Definition term20 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@SUBSET a0 x0 y0) /\ (~ ((@CARD a0 x0) = (@CARD a0 y0)))) -> @PSUBSET a0 x0 y0.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (x0 = x1)).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (~ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => ~ ((@CARD a0 y0) = (@CARD a0 x0))) x0.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@SUBSET a0 x0 y0) /\ (~ ((@CARD a0 x0) = (@CARD a0 y0)))) -> (@SUBSET a0 x0 y0) /\ (~ (x0 = y0)).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := ((@CARD a0 x0) = (@CARD a0 x0)) -> False.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@SUBSET a0 x0 y0) /\ (~ ((@CARD a0 x0) = (@CARD a0 y0)))) -> @PSUBSET a0 x0 y0.
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) -> False.
Definition term11 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1.
