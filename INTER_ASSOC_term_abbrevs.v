Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term76 := (~ False) -> False.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @INTER a0 x0 (@INTER a0 x1 x2).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term47 (x0 : Prop) := ~ (~ x0).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (x1 x2).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term39 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (((x0 y2) /\ (y0 y2)) /\ (y1 y2)) = ((x0 y2) /\ ((y0 y2) /\ (y1 y2))).
Definition term15 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (@IN a0 y3 (@INTER a0 (@INTER a0 y0 y1) y2)) = (@IN a0 y3 (@INTER a0 y0 (@INTER a0 y1 y2))).
Definition term14 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (@INTER a0 (@INTER a0 y0 y1) y2) = (@INTER a0 y0 (@INTER a0 y1 y2)).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@INTER a0 (@INTER a0 x0 y0) y1)) = (@IN a0 y2 (@INTER a0 x0 (@INTER a0 y0 y1))).
Definition term40 (x0 : Prop) := (~ x0) -> False.
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((((x0 x3) /\ (x1 x3)) /\ (x2 x3)) = ((x0 x3) /\ ((x1 x3) /\ (x2 x3))))) -> False.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((x0 x3) /\ (x1 x3)) /\ (x2 x3)) /\ ((~ (x0 x3)) \/ ((~ (x1 x3)) \/ (~ (x2 x3)))).
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @IN a0 x0 (@INTER a0 (@INTER a0 x1 x2) x3).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (((x0 x3) /\ (x1 x3)) /\ (x2 x3)).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term42 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3)))).
Definition term74 (x0 : Prop) := (~ x0) -> x0.
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((~ (x0 x2)) \/ (~ (x1 x2))).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (~ (((x0 x3) /\ (x1 x3)) /\ (x2 x3))).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (x0 x3) /\ ((x1 x3) /\ (x2 x3)).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@INTER a0 (@INTER a0 x0 y0) y1) = (@INTER a0 x0 (@INTER a0 y0 y1)).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (((x0 y0) /\ (x1 y0)) /\ (x2 y0)) = ((x0 y0) /\ ((x1 y0) /\ (x2 y0))).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x1 x2).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((x0 x3) /\ (x1 x3)) /\ (x2 x3)) /\ (~ ((x0 x3) /\ ((x1 x3) /\ (x2 x3)))).
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := and (@IN a0 x0 (@INTER a0 x1 x2)).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (x0 x3)) \/ ((~ (x1 x3)) \/ (~ (x2 x3))).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((x0 x3) /\ (x1 x3)) /\ (x2 x3).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ ((((x0 x3) /\ (x1 x3)) /\ (x2 x3)) = ((x0 x3) /\ ((x1 x3) /\ (x2 x3)))).
Definition term43 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))) -> False.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((((x0 x3) /\ (x1 x3)) /\ (x2 x3)) /\ ((~ (x0 x3)) \/ ((~ (x1 x3)) \/ (~ (x2 x3))))).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((x0 x2) /\ (x1 x2)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (((x0 y1) /\ (x1 y1)) /\ (y0 y1)) = ((x0 y1) /\ ((x1 y1) /\ (y0 y1))).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@INTER a0 (@INTER a0 x0 x1) y0)) = (@IN a0 y1 (@INTER a0 x0 (@INTER a0 x1 y0))).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (((x0 y0) /\ (x1 y0)) /\ (x2 y0)) = ((x0 y0) /\ ((x1 y0) /\ (x2 y0))).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INTER a0 (@INTER a0 x1 x2) x3)).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x0 x3) /\ (x1 x3))) \/ (~ (x2 x3)).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((((x0 x3) /\ (x1 x3)) /\ (x2 x3)) /\ (~ ((x0 x3) /\ ((x1 x3) /\ (x2 x3))))) \/ ((~ (((x0 x3) /\ (x1 x3)) /\ (x2 x3))) /\ ((x0 x3) /\ ((x1 x3) /\ (x2 x3)))).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 (@INTER a0 x0 x1) x2)) = (@IN a0 y0 (@INTER a0 x0 (@INTER a0 x1 x2))).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, (@INTER a0 (@INTER a0 x0 x1) y0) = (@INTER a0 x0 (@INTER a0 x1 y0)).
Definition term46 (a0 : Type') := ~ (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))).
Definition term41 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))) -> False.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((((x0 x3) /\ (x1 x3)) /\ (x2 x3)) /\ ((~ (x0 x3)) \/ ((~ (x1 x3)) \/ (~ (x2 x3))))) \/ ((((~ (x0 x3)) \/ (~ (x1 x3))) \/ (~ (x2 x3))) /\ ((x0 x3) /\ ((x1 x3) /\ (x2 x3)))).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop (((x0 x3) /\ (x1 x3)) /\ (x2 x3)).
Definition term44 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))) -> False.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@INTER a0 (@INTER a0 x0 y0) y1) = (@INTER a0 x0 (@INTER a0 y0 y1)).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := (@IN a0 x1 x0) /\ (@IN a0 x1 (@INTER a0 x2 x3)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (@INTER a0 (@INTER a0 x0 x1) y0) = (@INTER a0 x0 (@INTER a0 x1 y0)).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (@IN a0 x1 x2).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @INTER a0 (@INTER a0 x0 x1) x2.
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ ((x0 x3) /\ ((x1 x3) /\ (x2 x3))).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (~ (x1 x2)).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (~ ((x0 x2) /\ (x1 x2))).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> Prop) := (@IN a0 x2 (@INTER a0 x0 x1)) /\ (@IN a0 x2 x3).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (((x0 x3) /\ (x1 x3)) /\ (x2 x3))) /\ ((x0 x3) /\ ((x1 x3) /\ (x2 x3))).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((((x0 x3) /\ (x1 x3)) /\ (x2 x3)) /\ (~ ((x0 x3) /\ ((x1 x3) /\ (x2 x3))))).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INTER a0 (@INTER a0 x0 x1) x2)) = (@IN a0 y0 (@INTER a0 x0 (@INTER a0 x1 x2))).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (x0 x3)) \/ (~ ((x1 x3) /\ (x2 x3))).
Definition term38 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (((x0 y2) /\ (y0 y2)) /\ (y1 y2)) = ((x0 y2) /\ ((y0 y2) /\ (y1 y2))).
Definition term13 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (@IN a0 y3 (@INTER a0 (@INTER a0 y0 y1) y2)) = (@IN a0 y3 (@INTER a0 y0 (@INTER a0 y1 y2))).
Definition term12 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (@INTER a0 (@INTER a0 y0 y1) y2) = (@INTER a0 y0 (@INTER a0 y1 y2)).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@INTER a0 (@INTER a0 x0 y0) y1)) = (@IN a0 y2 (@INTER a0 x0 (@INTER a0 y0 y1))).
Definition term45 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y0 y3) /\ (y1 y3)) /\ (y2 y3)) = ((y0 y3) /\ ((y1 y3) /\ (y2 y3))))) -> False.
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x1 (@INTER a0 x2 x3)).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((~ (x0 x3)) \/ (~ (x1 x3))) \/ (~ (x2 x3))) /\ ((x0 x3) /\ ((x1 x3) /\ (x2 x3))).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x0 x3)) \/ (~ (x1 x3))) \/ (~ (x2 x3)).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) /\ (x1 x2)).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (((x0 y1) /\ (x1 y1)) /\ (y0 y1)) = ((x0 y1) /\ ((x1 y1) /\ (y0 y1))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@INTER a0 (@INTER a0 x0 x1) y0)) = (@IN a0 y1 (@INTER a0 x0 (@INTER a0 x1 y0))).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ (((x0 x3) /\ (x1 x3)) /\ (x2 x3)).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (((~ (x0 x3)) \/ (~ (x1 x3))) \/ (~ (x2 x3))).
