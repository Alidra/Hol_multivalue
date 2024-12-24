Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 => (@pairwise a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = True.
Definition term57 := (~ False) -> False.
Definition term43 (x0 : Prop) := ~ (~ x0).
Definition term50 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0)) x1.
Definition term36 (x0 : Prop) := (~ x0) -> False.
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (@IN a0 x2 (@INSERT a0 x0 (@EMPTY a0))) /\ (~ (x1 = x2)).
Definition term44 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := (~ (x0 x1 x2)) -> False.
Definition term26 (a0 : Type') (x0 : a0) (x1 : type1402 a0) := fun y0 : a0 => forall y1 : a0, ((y0 = x0) /\ ((y1 = x0) /\ (~ (y0 = y1)))) -> x1 y0 y1.
Definition term25 (a0 : Type') (x0 : a0) (x1 : type1402 a0) := fun y0 : a0 => forall y1 : a0, ((@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))) /\ ((@IN a0 y1 (@INSERT a0 x0 (@EMPTY a0))) /\ (~ (y0 = y1)))) -> x1 y0 y1.
Definition term20 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((x2 = x0) /\ ((x3 = x0) /\ (~ (x2 = x3)))) -> x1 x2 x3.
Definition term38 (a0 : Type') := ~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3).
Definition term55 (x0 : Prop) := (~ x0) -> x0.
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@INSERT a0 y1 (@EMPTY a0))) = (y0 = y1)) x0.
Definition term29 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((y1 = y0) /\ ((y2 = y0) /\ (~ (y1 = y2)))) -> x0 y1 y2.
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (x1 = x0) /\ ((x2 = x0) /\ (~ (x1 = x2))).
Definition term34 (a0 : Type') := forall y0 : type1402 a0, forall y1 : a0, (@pairwise a0 y0 (@INSERT a0 y1 (@EMPTY a0))) = True.
Definition term52 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (x0 = y0)) x1.
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (@IN a0 x1 (@INSERT a0 x0 (@EMPTY a0))) /\ ((@IN a0 x2 (@INSERT a0 x0 (@EMPTY a0))) /\ (~ (x1 = x2))).
Definition term39 (a0 : Type') := ((~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) -> False) -> (~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) -> False.
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0) := and (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0))).
Definition term33 (a0 : Type') := fun y0 : type1402 a0 => forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3.
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 = y0)) x1).
Definition term31 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, ((y1 = y0) /\ ((y2 = y0) /\ (~ (y1 = y2)))) -> x0 y1 y2.
Definition term19 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((@IN a0 x2 (@INSERT a0 x0 (@EMPTY a0))) /\ ((@IN a0 x3 (@INSERT a0 x0 (@EMPTY a0))) /\ (~ (x2 = x3)))) -> x1 x2 x3.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : type1402 a0, (@pairwise a0 y1 y0) = (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y0) /\ ((@IN a0 y3 y0) /\ (~ (y2 = y3)))) -> y1 y2 y3)) x0.
Definition term42 (a0 : Type') := ~ (~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)).
Definition term37 (a0 : Type') := (~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) -> False.
Definition term21 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := fun y0 : a0 => ((@IN a0 x2 (@INSERT a0 x0 (@EMPTY a0))) /\ ((@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))) /\ (~ (x2 = y0)))) -> x1 x2 y0.
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) := and (x0 = x1).
Definition term40 (a0 : Type') := (((~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) -> False) -> (~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) -> False) -> (~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) -> False.
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term32 (a0 : Type') := fun y0 : type1402 a0 => forall y1 : a0, (@pairwise a0 y0 (@INSERT a0 y1 (@EMPTY a0))) = True.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := imp ((x1 = x0) /\ ((x2 = x0) /\ (~ (x1 = x2)))).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := imp ((@IN a0 x1 (@INSERT a0 x0 (@EMPTY a0))) /\ ((@IN a0 x2 (@INSERT a0 x0 (@EMPTY a0))) /\ (~ (x1 = x2)))).
Definition term22 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := fun y0 : a0 => ((x2 = x0) /\ ((y0 = x0) /\ (~ (x2 = y0)))) -> x1 x2 y0.
Definition term45 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (x0 = y0).
Definition term24 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := forall y0 : a0, ((x2 = x0) /\ ((y0 = x0) /\ (~ (x2 = y0)))) -> x1 x2 y0.
Definition term23 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := forall y0 : a0, ((@IN a0 x2 (@INSERT a0 x0 (@EMPTY a0))) /\ ((@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))) /\ (~ (x2 = y0)))) -> x1 x2 y0.
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (x2 = x0) /\ (~ (x1 = x2)).
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term27 (a0 : Type') (x0 : a0) (x1 : type1402 a0) := forall y0 : a0, forall y1 : a0, ((y0 = x0) /\ ((y1 = x0) /\ (~ (y0 = y1)))) -> x1 y0 y1.
Definition term9 (a0 : Type') (x0 : a0) (x1 : type1402 a0) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))) /\ ((@IN a0 y1 (@INSERT a0 x0 (@EMPTY a0))) /\ (~ (y0 = y1)))) -> x1 y0 y1.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ (~ (y0 = y1)))) -> x1 y0 y1.
Definition term54 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term30 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, (@pairwise a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = True.
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0).
Definition term8 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := @pairwise a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term49 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term58 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := ~ (x0 x1 x2).
Definition term35 (a0 : Type') := forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3.
Definition term41 (a0 : Type') := (((~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) -> False) -> (~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) -> False) -> ((~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) -> False) -> (~ (forall y0 : type1402 a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y2 = y1) /\ ((y3 = y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) -> False.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) := (fun y0 : type1402 a0 => (@pairwise a0 y0 x0) = (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 x0) /\ ((@IN a0 y2 x0) /\ (~ (y1 = y2)))) -> y0 y1 y2)) x1.
Definition term56 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : type1402 a0, (@pairwise a0 y0 x0) = (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 x0) /\ ((@IN a0 y2 x0) /\ (~ (y1 = y2)))) -> y0 y1 y2).
Definition term51 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x0.
