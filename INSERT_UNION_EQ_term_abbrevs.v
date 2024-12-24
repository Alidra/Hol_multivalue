Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term43 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))).
Definition term15 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (@IN a0 y3 (@UNION a0 (@INSERT a0 y0 y1) y2)) = (@IN a0 y3 (@INSERT a0 y0 (@UNION a0 y1 y2))).
Definition term14 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (@UNION a0 (@INSERT a0 y0 y1) y2) = (@INSERT a0 y0 (@UNION a0 y1 y2)).
Definition term89 := (~ False) -> False.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 (@UNION a0 x2 x3)).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((x3 = x0) \/ (x1 x3)) \/ (x2 x3).
Definition term51 (x0 : Prop) := ~ (~ x0).
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ ((~ (x3 = x0)) /\ ((~ (x1 x3)) /\ (~ (x2 x3))))) \/ ((((~ (x3 = x0)) /\ (~ (x1 x3))) /\ (~ (x2 x3))) /\ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3)))).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) \/ (x1 x2)).
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) \/ (x1 x2).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term41 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (((y2 = x0) \/ (y0 y2)) \/ (y1 y2)) = ((y2 = x0) \/ ((y0 y2) \/ (y1 y2))).
Definition term11 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@UNION a0 (@INSERT a0 x0 y0) y1)) = (@IN a0 y2 (@INSERT a0 x0 (@UNION a0 y0 y1))).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term44 (x0 : Prop) := (~ x0) -> False.
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) = ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))))) -> False.
Definition term42 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))).
Definition term13 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (@IN a0 y3 (@UNION a0 (@INSERT a0 y0 y1) y2)) = (@IN a0 y3 (@INSERT a0 y0 (@UNION a0 y1 y2))).
Definition term12 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (@UNION a0 (@INSERT a0 y0 y1) y2) = (@INSERT a0 y0 (@UNION a0 y1 y2)).
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @IN a0 x0 (@UNION a0 (@INSERT a0 x1 x2) x3).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term87 (x0 : Prop) := (~ x0) -> x0.
Definition term8 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@UNION a0 (@INSERT a0 x0 y0) y1) = (@INSERT a0 x0 (@UNION a0 y0 y1)).
Definition term60 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x3 = x0)) /\ (~ (x1 x3))) /\ (~ (x2 x3)).
Definition term67 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 (@UNION a0 x2 x3)).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x2 = x0) \/ (x1 x2)).
Definition term83 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term74 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ ((~ (x3 = x0)) /\ ((~ (x1 x3)) /\ (~ (x2 x3)))).
Definition term55 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x2 = x0)) /\ (~ (x1 x2)).
Definition term47 (a0 : Type') := ((~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))) -> False) -> (~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))) -> False.
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (((y1 = x0) \/ (x1 y1)) \/ (y0 y1)) = ((y1 = x0) \/ ((x1 y1) \/ (y0 y1))).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@UNION a0 (@INSERT a0 x0 x1) y0)) = (@IN a0 y1 (@INSERT a0 x0 (@UNION a0 x1 y0))).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))).
Definition term64 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (x0 = x1)).
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@UNION a0 (@INSERT a0 x1 x2) x3)).
Definition term84 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term72 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)).
Definition term71 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((~ (x3 = x0)) /\ (~ (x1 x3))) /\ (~ (x2 x3))) /\ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) /\ (~ (x1 x2)).
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@UNION a0 (@INSERT a0 x0 x1) x2)) = (@IN a0 y0 (@INSERT a0 x0 (@UNION a0 x1 x2))).
Definition term69 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (((~ (x3 = x0)) /\ (~ (x1 x3))) /\ (~ (x2 x3))).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, (@UNION a0 (@INSERT a0 x0 x1) y0) = (@INSERT a0 x0 (@UNION a0 x1 y0)).
Definition term50 (a0 : Type') := ~ (~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))).
Definition term45 (a0 : Type') := (~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))) -> False.
Definition term57 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := and (~ ((x2 = x0) \/ (x1 x2))).
Definition term48 (a0 : Type') := (((~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))) -> False) -> (~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))) -> False) -> (~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))) -> False.
Definition term58 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := and ((~ (x2 = x0)) /\ (~ (x1 x2))).
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term10 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@UNION a0 (@INSERT a0 x0 y0) y1) = (@INSERT a0 x0 (@UNION a0 y0 y1)).
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := or (@IN a0 x0 (@INSERT a0 x1 x2)).
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) y0) = (@INSERT a0 x0 (@UNION a0 x1 y0)).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) \/ (x1 x2).
Definition term76 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ ((~ (x3 = x0)) /\ ((~ (x1 x3)) /\ (~ (x2 x3))))).
Definition term66 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (x3 = x0)) /\ ((~ (x1 x3)) /\ (~ (x2 x3))).
Definition term86 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term70 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (((x3 = x0) \/ (x1 x3)) \/ (x2 x3))) /\ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))).
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) = ((x3 = x0) \/ ((x1 x3) \/ (x2 x3)))).
Definition term75 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ (~ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))))).
Definition term80 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term46 (a0 : Type') := ~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3)))).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> Prop) := (@IN a0 x2 (@INSERT a0 x0 x1)) \/ (@IN a0 x2 x3).
Definition term68 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (~ (((x3 = x0) \/ (x1 x3)) \/ (x2 x3))).
Definition term61 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNION a0 (@INSERT a0 x0 x1) x2)) = (@IN a0 y0 (@INSERT a0 x0 (@UNION a0 x1 x2))).
Definition term40 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (((y2 = x0) \/ (y0 y2)) \/ (y1 y2)) = ((y2 = x0) \/ ((y0 y2) \/ (y1 y2))).
Definition term9 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@UNION a0 (@INSERT a0 x0 y0) y1)) = (@IN a0 y2 (@INSERT a0 x0 (@UNION a0 y0 y1))).
Definition term49 (a0 : Type') := (((~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))) -> False) -> (~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))) -> False) -> ((~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))) -> False) -> (~ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y3 = y0) \/ (y1 y3)) \/ (y2 y3)) = ((y3 = y0) \/ ((y1 y3) \/ (y2 y3))))) -> False.
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @UNION a0 (@INSERT a0 x0 x1) x2.
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (@IN a0 x0 x1).
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (x3 = x0)) /\ (~ ((x1 x3) \/ (x2 x3))).
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (x3 = x0) \/ ((x1 x3) \/ (x2 x3)).
Definition term73 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ (~ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3)))).
Definition term59 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x3 = x0) \/ (x1 x3))) /\ (~ (x2 x3)).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term88 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)).
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or ((x2 = x0) \/ (x1 x2)).
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (((y1 = x0) \/ (x1 y1)) \/ (y0 y1)) = ((y1 = x0) \/ ((x1 y1) \/ (y0 y1))).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@UNION a0 (@INSERT a0 x0 x1) y0)) = (@IN a0 y1 (@INSERT a0 x0 (@UNION a0 x1 y0))).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @INSERT a0 x0 (@UNION a0 x1 x2).
Definition term82 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x0.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
Definition term77 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ (~ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))))) \/ ((~ (((x3 = x0) \/ (x1 x3)) \/ (x2 x3))) /\ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3)))).
