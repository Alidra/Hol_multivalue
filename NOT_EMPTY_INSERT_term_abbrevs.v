Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((y0 = x0) \/ (x1 y0)).
Definition term67 := (~ False) -> False.
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@EMPTY a0)) = (@IN a0 y0 (@INSERT a0 x0 x1)).
Definition term4 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => ~ ((@EMPTY a0) = (@INSERT a0 x0 y0)).
Definition term33 (x0 : Prop) := ~ (~ x0).
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (forall y0 : a0, (@IN a0 y0 (@EMPTY a0)) = (@IN a0 y0 (@INSERT a0 x0 x1))).
Definition term50 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => ~ (y1 = x0)) y0) /\ ((fun y1 : a0 => ~ (x1 y1)) y0).
Definition term43 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) \/ (x1 x2).
Definition term61 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (forall y0 : a0, ~ (y0 = x0)) /\ (forall y0 : a0, ~ (x1 y0)).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term56 (a0 : Type') (x0 : a0) := and (forall y0 : a0, (fun y1 : a0 => ~ (y1 = x0)) y0).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term26 (x0 : Prop) := (~ x0) -> False.
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) -> False.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term64 (x0 : Prop) := (~ x0) -> x0.
Definition term25 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))).
Definition term11 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, (@IN a0 y2 (@EMPTY a0)) = (@IN a0 y2 (@INSERT a0 y0 y1))).
Definition term10 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, ~ ((@EMPTY a0) = (@INSERT a0 y0 y1)).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term8 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, ~ ((@EMPTY a0) = (@INSERT a0 y0 y1)).
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, ((fun y1 : a0 => ~ (y1 = x0)) y0) /\ ((fun y1 : a0 => ~ (x1 y1)) y0).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x2 = x0) \/ (x1 x2)).
Definition term22 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => ~ (forall y1 : a0, ~ ((y1 = x0) \/ (y0 y1))).
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, (~ (y0 = x0)) /\ (~ (x1 y0))).
Definition term63 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term68 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (forall y0 : a0, ~ ((y0 = x0) \/ (x1 y0))) -> False.
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x2 = x0)) /\ (~ (x1 x2)).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term29 (a0 : Type') := ((~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))) -> False) -> (~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))) -> False.
Definition term55 (a0 : Type') (x0 : a0) := forall y0 : a0, ~ (y0 = x0).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (~ (y0 = x0)) /\ (~ (x1 y0)).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (x0 = x1)).
Definition term23 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, ~ (forall y1 : a0, ~ ((y1 = x0) \/ (y0 y1))).
Definition term7 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, ~ (forall y1 : a0, (@IN a0 y1 (@EMPTY a0)) = (@IN a0 y1 (@INSERT a0 x0 y0))).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0) := and ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term6 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, ~ ((@EMPTY a0) = (@INSERT a0 x0 y0)).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ~ ((y0 = x0) \/ (x1 y0))).
Definition term32 (a0 : Type') := ~ (~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))).
Definition term27 (a0 : Type') := (~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))) -> False.
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (y0 = x0)) /\ (~ (x1 y0)).
Definition term30 (a0 : Type') := (((~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))) -> False) -> (~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))) -> False) -> (~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))) -> False.
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term62 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term53 (a0 : Type') (x0 : a0) := fun y0 : a0 => (fun y1 : a0 => ~ (y1 = x0)) y0.
Definition term5 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => ~ (forall y1 : a0, (@IN a0 y1 (@EMPTY a0)) = (@IN a0 y1 (@INSERT a0 x0 y0))).
Definition term41 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term28 (a0 : Type') := ~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2)))).
Definition term12 (a0 : Type') (x0 : a0) := @eq Prop (@IN a0 x0 (@EMPTY a0)).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((@EMPTY a0) = (@INSERT a0 x0 x1)).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term40 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (forall y0 : a0, (fun y1 : a0 => ~ (y1 = x0)) y0) /\ (forall y0 : a0, (fun y1 : a0 => ~ (x1 y1)) y0).
Definition term31 (a0 : Type') := (((~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))) -> False) -> (~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))) -> False) -> ((~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))) -> False) -> (~ (forall y0 : a0, forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))))) -> False.
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((fun y0 : a0 => ~ (y0 = x0)) x2) /\ ((fun y0 : a0 => ~ (x1 y0)) x2).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, ~ ((y0 = x0) \/ (x1 y0)).
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, ((fun y1 : a0 => ~ (y1 = x0)) y0) /\ ((fun y1 : a0 => ~ (x1 y1)) y0)).
Definition term24 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, ~ (forall y2 : a0, ~ ((y2 = y0) \/ (y1 y2))).
Definition term9 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, ~ (forall y2 : a0, (@IN a0 y2 (@EMPTY a0)) = (@IN a0 y2 (@INSERT a0 y0 y1))).
Definition term66 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@EMPTY a0)) = (@IN a0 y0 (@INSERT a0 x0 x1)).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term54 (a0 : Type') (x0 : a0) := forall y0 : a0, (fun y1 : a0 => ~ (y1 = x0)) y0.
Definition term57 (a0 : Type') (x0 : a0) := and (forall y0 : a0, ~ (y0 = x0)).