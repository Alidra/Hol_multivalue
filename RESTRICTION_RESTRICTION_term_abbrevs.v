Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> x1 y0.
Definition term134 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (~ (x0 x3)) /\ (~ ((~ (x1 x3)) \/ ((@ARB a1) = (x2 x3)))).
Definition term146 := (~ False) -> False.
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (forall y0 : a0, (x0 y0) -> x1 y0).
Definition term79 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 False (@COND a1 (x0 x2) (x1 x2) (@ARB a1)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := fun y0 : a0 => (@COND a1 (@IN a0 y0 x1) (@COND a1 (@IN a0 y0 x0) (x2 y0) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y0 x1) (x2 y0) (@ARB a1)).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @COND a1 (@IN a0 x3 x0) (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1)) (@ARB a1).
Definition term78 (x0 : Prop) := ~ (~ x0).
Definition term132 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := ~ ((~ (x0 x2)) \/ ((@ARB a1) = (x1 x2))).
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) \/ (~ (x1 x2)).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and ((~ (x0 x1)) \/ True).
Definition term117 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (forall y2 : a0, (x0 y2) -> y0 y2) -> forall y2 : a0, (y0 y2) \/ ((~ (x0 y2)) \/ ((@ARB a1) = (y1 y2))).
Definition term67 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (forall y2 : a0, (x0 y2) -> y0 y2) -> forall y2 : a0, (@COND a1 (x0 y2) (@COND a1 (y0 y2) (y1 y2) (@ARB a1)) (@ARB a1)) = (@COND a1 (x0 y2) (y1 y2) (@ARB a1)).
Definition term43 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (forall y2 : a0, (@IN a0 y2 x0) -> @IN a0 y2 y0) -> forall y2 : a0, (@COND a1 (@IN a0 y2 x0) (@COND a1 (@IN a0 y2 y0) (y1 y2) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y2 x0) (y1 y2) (@ARB a1)).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@SUBSET a0 x0 y0) -> forall y2 : a0, (@COND a1 (@IN a0 y2 x0) (@COND a1 (@IN a0 y2 y0) (y1 y2) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y2 x0) (y1 y2) (@ARB a1)).
Definition term127 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := ~ ((@ARB a1) = (x0 x1)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, (@RESTRICTION a0 a1 x0 y0 y1) = (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1))) x1.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (@RESTRICTION a0 a1 x0 x1 y0) = (@COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1))) x2.
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term120 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (y1 y3) \/ ((~ (y0 y3)) \/ ((@ARB a1) = (y2 y3))).
Definition term70 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)).
Definition term46 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (@IN a0 y3 y0) -> @IN a0 y3 y1) -> forall y3 : a0, (@COND a1 (@IN a0 y3 y0) (@COND a1 (@IN a0 y3 y1) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y3 y0) (y2 y3) (@ARB a1)).
Definition term37 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (@SUBSET a0 y0 y1) -> forall y3 : a0, (@COND a1 (@IN a0 y3 y0) (@COND a1 (@IN a0 y3 y1) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y3 y0) (y2 y3) (@ARB a1)).
Definition term36 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (@SUBSET a0 y0 y1) -> (@RESTRICTION a0 a1 y0 (@RESTRICTION a0 a1 y1 y2)) = (@RESTRICTION a0 a1 y0 y2).
Definition term71 (x0 : Prop) := (~ x0) -> False.
Definition term121 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (~ ((x0 x3) \/ ((~ (x1 x3)) \/ ((@ARB a1) = (x2 x3))))) -> False.
Definition term107 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := ((~ (x0 x3)) \/ True) /\ ((x0 x3) \/ ((~ (x1 x3)) \/ ((@ARB a1) = (x2 x3)))).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : a0, (@RESTRICTION a0 a1 y0 y1 y2) = (@COND a1 (@IN a0 y2 y0) (y1 y2) (@ARB a1))) x0.
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (~ (x0 x1))).
Definition term142 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term99 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (~ (x0 x2)) \/ ((@ARB a1) = (x1 x2)).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @RESTRICTION a0 a1 x0 (@RESTRICTION a0 a1 x1 x2) x3.
Definition term64 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := (forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (@COND a1 (x1 y0) (@COND a1 (x0 y0) (x2 y0) (@ARB a1)) (@ARB a1)) = (@COND a1 (x1 y0) (x2 y0) (@ARB a1)).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := (forall y0 : a0, (@IN a0 y0 x1) -> @IN a0 y0 x0) -> forall y0 : a0, (@COND a1 (@IN a0 y0 x1) (@COND a1 (@IN a0 y0 x0) (x2 y0) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y0 x1) (x2 y0) (@ARB a1)).
Definition term90 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (((x0 x3) = False) -> ((@COND a1 (x0 x3) (@COND a1 (x1 x3) (x2 x3) (@ARB a1)) (@ARB a1)) = (@COND a1 (x0 x3) (x2 x3) (@ARB a1))) = True) /\ (((x0 x3) = True) -> ((@COND a1 (x0 x3) (@COND a1 (x1 x3) (x2 x3) (@ARB a1)) (@ARB a1)) = (@COND a1 (x0 x3) (x2 x3) (@ARB a1))) = ((@COND a1 (x1 x3) (x2 x3) (@ARB a1)) = (x2 x3))).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (@SUBSET a0 x0 x1).
Definition term73 (a0 : Type') (a1 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1))).
Definition term87 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @COND a1 True (x0 x1).
Definition term112 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := fun y0 : a0 => (x0 y0) \/ ((~ (x1 y0)) \/ ((@ARB a1) = (x2 y0))).
Definition term138 (x0 : Prop) := (~ x0) -> x0.
Definition term60 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @COND a1 (x0 x3) (@COND a1 (x1 x3) (x2 x3) (@ARB a1)) (@ARB a1).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) \/ True.
Definition term93 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x2 x3)) \/ ((@COND a1 (x0 x3) (x1 x3) (@ARB a1)) = (x1 x3))) /\ ((x2 x3) \/ True).
Definition term114 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := (forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) \/ ((~ (x1 y0)) \/ ((@ARB a1) = (x2 y0))).
Definition term86 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @eq a1 (@COND a1 (x0 x2) (x1 x2) (@ARB a1)).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@SUBSET a0 x0 y0) -> (@RESTRICTION a0 a1 x0 (@RESTRICTION a0 a1 y0 y1)) = (@RESTRICTION a0 a1 x0 y1).
Definition term101 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @eq a1 (x0 x1).
Definition term83 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := ((x1 x3) = False) -> ((@COND a1 (x1 x3) (@COND a1 (x0 x3) (x2 x3) (@ARB a1)) (@ARB a1)) = (@COND a1 (x1 x3) (x2 x3) (@ARB a1))) = True.
Definition term106 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := ((((x0 x3) = False) -> ((~ (x1 x3)) \/ ((@COND a1 (x0 x3) (x2 x3) (@ARB a1)) = (x2 x3))) = ((~ (x1 x3)) \/ ((@ARB a1) = (x2 x3)))) /\ (((x0 x3) = True) -> ((~ (x1 x3)) \/ ((@COND a1 (x0 x3) (x2 x3) (@ARB a1)) = (x2 x3))) = True)) -> ((~ (x1 x3)) \/ ((@COND a1 (x0 x3) (x2 x3) (@ARB a1)) = (x2 x3))) = (((~ (x0 x3)) \/ True) /\ ((x0 x3) \/ ((~ (x1 x3)) \/ ((@ARB a1) = (x2 x3))))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := @RESTRICTION a0 a1 x0 (@RESTRICTION a0 a1 x1 x2).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (x0 x2))) -> x1 x2.
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := (@SUBSET a0 x1 x0) -> (@RESTRICTION a0 a1 x1 (@RESTRICTION a0 a1 x0 x2)) = (@RESTRICTION a0 a1 x1 x2).
Definition term59 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @COND a1 (x0 x3) (@COND a1 (x1 x3) (x2 x3) (@ARB a1)).
Definition term92 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ((((x2 x3) = False) -> ((@COND a1 (x2 x3) (@COND a1 (x0 x3) (x1 x3) (@ARB a1)) (@ARB a1)) = (@COND a1 (x2 x3) (x1 x3) (@ARB a1))) = True) /\ (((x2 x3) = True) -> ((@COND a1 (x2 x3) (@COND a1 (x0 x3) (x1 x3) (@ARB a1)) (@ARB a1)) = (@COND a1 (x2 x3) (x1 x3) (@ARB a1))) = ((@COND a1 (x0 x3) (x1 x3) (@ARB a1)) = (x1 x3)))) -> ((@COND a1 (x2 x3) (@COND a1 (x0 x3) (x1 x3) (@ARB a1)) (@ARB a1)) = (@COND a1 (x2 x3) (x1 x3) (@ARB a1))) = (((~ (x2 x3)) \/ ((@COND a1 (x0 x3) (x1 x3) (@ARB a1)) = (x1 x3))) /\ ((x2 x3) \/ True)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1).
Definition term62 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := fun y0 : a0 => (@COND a1 (x1 y0) (@COND a1 (x0 y0) (x2 y0) (@ARB a1)) (@ARB a1)) = (@COND a1 (x1 y0) (x2 y0) (@ARB a1)).
Definition term74 (a0 : Type') (a1 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))) -> False.
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (~ (~ (x0 x1))).
Definition term116 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> a1, (forall y1 : a0, (x1 y1) -> x0 y1) -> forall y1 : a0, (x0 y1) \/ ((~ (x1 y1)) \/ ((@ARB a1) = (y0 y1))).
Definition term66 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> a1, (forall y1 : a0, (x1 y1) -> x0 y1) -> forall y1 : a0, (@COND a1 (x1 y1) (@COND a1 (x0 y1) (y0 y1) (@ARB a1)) (@ARB a1)) = (@COND a1 (x1 y1) (y0 y1) (@ARB a1)).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> a1, (forall y1 : a0, (@IN a0 y1 x1) -> @IN a0 y1 x0) -> forall y1 : a0, (@COND a1 (@IN a0 y1 x1) (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y1 x1) (y0 y1) (@ARB a1)).
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((~ (x0 x2)) \/ (x1 x2)).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) \/ True.
Definition term95 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := and ((~ (x0 x3)) \/ ((@COND a1 (x1 x3) (x2 x3) (@ARB a1)) = (x2 x3))).
Definition term85 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 True (@COND a1 (x0 x2) (x1 x2) (@ARB a1)) (@ARB a1).
Definition term81 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @COND a1 False (x0 x1).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := fun y0 : a0 => (@RESTRICTION a0 a1 x1 (@RESTRICTION a0 a1 x0 x2) y0) = (@RESTRICTION a0 a1 x1 x2 y0).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term55 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0) := @COND a1 (x0 x1).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> a1, (@SUBSET a0 x1 x0) -> (@RESTRICTION a0 a1 x1 (@RESTRICTION a0 a1 x0 y0)) = (@RESTRICTION a0 a1 x1 y0).
Definition term110 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := True /\ ((x0 x3) \/ ((~ (x1 x3)) \/ ((@ARB a1) = (x2 x3)))).
Definition term130 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (~ (~ (x0 x2))) /\ (~ ((@ARB a1) = (x1 x2))).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := forall y0 : a0, (@RESTRICTION a0 a1 x1 (@RESTRICTION a0 a1 x0 x2) y0) = (@RESTRICTION a0 a1 x1 x2 y0).
Definition term77 (a0 : Type') (a1 : Type') := ~ (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))).
Definition term72 (a0 : Type') (a1 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))) -> False.
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1).
Definition term96 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := ((~ (x0 x3)) \/ ((@COND a1 (x1 x3) (x2 x3) (@ARB a1)) = (x2 x3))) /\ True.
Definition term75 (a0 : Type') (a1 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))) -> False.
Definition term89 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := ((x0 x3) = True) -> ((@COND a1 (x0 x3) (@COND a1 (x1 x3) (x2 x3) (@ARB a1)) (@ARB a1)) = (@COND a1 (x0 x3) (x2 x3) (@ARB a1))) = ((@COND a1 (x1 x3) (x2 x3) (@ARB a1)) = (x2 x3)).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term118 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (forall y2 : a0, (x0 y2) -> y0 y2) -> forall y2 : a0, (y0 y2) \/ ((~ (x0 y2)) \/ ((@ARB a1) = (y1 y2))).
Definition term68 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (forall y2 : a0, (x0 y2) -> y0 y2) -> forall y2 : a0, (@COND a1 (x0 y2) (@COND a1 (y0 y2) (y1 y2) (@ARB a1)) (@ARB a1)) = (@COND a1 (x0 y2) (y1 y2) (@ARB a1)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (forall y2 : a0, (@IN a0 y2 x0) -> @IN a0 y2 y0) -> forall y2 : a0, (@COND a1 (@IN a0 y2 x0) (@COND a1 (@IN a0 y2 y0) (y1 y2) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y2 x0) (y1 y2) (@ARB a1)).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (@SUBSET a0 x0 y0) -> forall y2 : a0, (@COND a1 (@IN a0 y2 x0) (@COND a1 (@IN a0 y2 y0) (y1 y2) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y2 x0) (y1 y2) (@ARB a1)).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (@SUBSET a0 x0 y0) -> (@RESTRICTION a0 a1 x0 (@RESTRICTION a0 a1 y0 y1)) = (@RESTRICTION a0 a1 x0 y1).
Definition term56 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 (@IN a0 x2 x0) (x1 x2).
Definition term100 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := ((x0 x3) = False) -> ((~ (x1 x3)) \/ ((@COND a1 (x0 x3) (x2 x3) (@ARB a1)) = (x2 x3))) = ((~ (x1 x3)) \/ ((@ARB a1) = (x2 x3))).
Definition term63 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := forall y0 : a0, (@COND a1 (x1 y0) (@COND a1 (x0 y0) (x2 y0) (@ARB a1)) (@ARB a1)) = (@COND a1 (x1 y0) (x2 y0) (@ARB a1)).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := forall y0 : a0, (@COND a1 (@IN a0 y0 x1) (@COND a1 (@IN a0 y0 x0) (x2 y0) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y0 x1) (x2 y0) (@ARB a1)).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term91 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x2 = False) -> x0 = x3) /\ ((x2 = True) -> x0 = x1)) -> x0 = (((~ x2) \/ x1) /\ (x2 \/ x3)).
Definition term111 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @eq Prop ((@COND a1 (x1 x3) (@COND a1 (x0 x3) (x2 x3) (@ARB a1)) (@ARB a1)) = (@COND a1 (x1 x3) (x2 x3) (@ARB a1))).
Definition term115 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> a1 => (forall y1 : a0, (x1 y1) -> x0 y1) -> forall y1 : a0, (x0 y1) \/ ((~ (x1 y1)) \/ ((@ARB a1) = (y0 y1))).
Definition term65 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> a1 => (forall y1 : a0, (x1 y1) -> x0 y1) -> forall y1 : a0, (@COND a1 (x1 y1) (@COND a1 (x0 y1) (y0 y1) (@ARB a1)) (@ARB a1)) = (@COND a1 (x1 y1) (y0 y1) (@ARB a1)).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> a1 => (forall y1 : a0, (@IN a0 y1 x1) -> @IN a0 y1 x0) -> forall y1 : a0, (@COND a1 (@IN a0 y1 x1) (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y1 x1) (y0 y1) (@ARB a1)).
Definition term105 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (((x1 x3) = False) -> ((~ (x0 x3)) \/ ((@COND a1 (x1 x3) (x2 x3) (@ARB a1)) = (x2 x3))) = ((~ (x0 x3)) \/ ((@ARB a1) = (x2 x3)))) /\ (((x1 x3) = True) -> ((~ (x0 x3)) \/ ((@COND a1 (x1 x3) (x2 x3) (@ARB a1)) = (x2 x3))) = True).
Definition term135 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (~ (x0 x3)) /\ ((x1 x3) /\ (~ ((@ARB a1) = (x2 x3)))).
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (~ (x0 y0)) \/ (x1 y0)) x2.
Definition term84 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 True (@COND a1 (x0 x2) (x1 x2) (@ARB a1)).
Definition term58 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 (x0 x2) (x1 x2) (@ARB a1).
Definition term80 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 False (@COND a1 (x0 x2) (x1 x2) (@ARB a1)) (@ARB a1).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) -> x1 x2.
Definition term141 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((x0 x2) \/ (~ (x1 x2))).
Definition term82 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @COND a1 False (x0 x1) (@ARB a1).
Definition term113 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := forall y0 : a0, (x0 y0) \/ ((~ (x1 y0)) \/ ((@ARB a1) = (x2 y0))).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (x1 x2).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @eq a1 (@RESTRICTION a0 a1 x0 (@RESTRICTION a0 a1 x1 x2) x3).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> a1 => (@SUBSET a0 x1 x0) -> forall y1 : a0, (@COND a1 (@IN a0 y1 x1) (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y1 x1) (y0 y1) (@ARB a1)).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (x0 y0)) \/ (x1 y0).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @COND a1 (@IN a0 x3 x0) (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @COND a1 (@IN a0 x3 x0) (@RESTRICTION a0 a1 x1 x2 x3).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @eq a1 (@COND a1 (@IN a0 x3 x0) (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1)) (@ARB a1)).
Definition term122 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := ~ ((x0 x3) \/ ((~ (x1 x3)) \/ ((@ARB a1) = (x2 x3)))).
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> a1, (@SUBSET a0 x1 x0) -> forall y1 : a0, (@COND a1 (@IN a0 y1 x1) (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y1 x1) (y0 y1) (@ARB a1)).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x1 y0.
Definition term119 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (y1 y3) \/ ((~ (y0 y3)) \/ ((@ARB a1) = (y2 y3))).
Definition term69 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)).
Definition term45 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (@IN a0 y3 y0) -> @IN a0 y3 y1) -> forall y3 : a0, (@COND a1 (@IN a0 y3 y0) (@COND a1 (@IN a0 y3 y1) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y3 y0) (y2 y3) (@ARB a1)).
Definition term35 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (@SUBSET a0 y0 y1) -> forall y3 : a0, (@COND a1 (@IN a0 y3 y0) (@COND a1 (@IN a0 y3 y1) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y3 y0) (y2 y3) (@ARB a1)).
Definition term34 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (@SUBSET a0 y0 y1) -> (@RESTRICTION a0 a1 y0 (@RESTRICTION a0 a1 y1 y2)) = (@RESTRICTION a0 a1 y0 y2).
Definition term76 (a0 : Type') (a1 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (forall y3 : a0, (y0 y3) -> y1 y3) -> forall y3 : a0, (@COND a1 (y0 y3) (@COND a1 (y1 y3) (y2 y3) (@ARB a1)) (@ARB a1)) = (@COND a1 (y0 y3) (y2 y3) (@ARB a1)))) -> False.
Definition term57 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 (x0 x2) (x1 x2).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ (x0 y0)) \/ (x1 y0).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) -> @IN a0 x1 x2.
Definition term104 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := ((x1 x3) = True) -> ((~ (x0 x3)) \/ ((@COND a1 (x1 x3) (x2 x3) (@ARB a1)) = (x2 x3))) = True.
Definition term97 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (~ (x0 x3)) \/ ((@COND a1 (x1 x3) (x2 x3) (@ARB a1)) = (x2 x3)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term108 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (x0 x3) \/ ((~ (x1 x3)) \/ ((@ARB a1) = (x2 x3))).
Definition term88 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @COND a1 True (x0 x1) (@ARB a1).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (x0 x1)).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : a0, (@RESTRICTION a0 a1 x0 y0 y1) = (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1)).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND a1 (@IN a0 x0 x1).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> a1 => (@SUBSET a0 x1 x0) -> (@RESTRICTION a0 a1 x1 (@RESTRICTION a0 a1 x0 y0)) = (@RESTRICTION a0 a1 x1 y0).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term61 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @eq a1 (@COND a1 (x0 x3) (@COND a1 (x1 x3) (x2 x3) (@ARB a1)) (@ARB a1)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @COND a1 (@IN a0 x3 x0) (@RESTRICTION a0 a1 x1 x2 x3) (@ARB a1).
Definition term131 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (x0 x2) /\ (~ ((@ARB a1) = (x1 x2))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, (@RESTRICTION a0 a1 x0 x1 y0) = (@COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := (@SUBSET a0 x1 x0) -> forall y0 : a0, (@COND a1 (@IN a0 y0 x1) (@COND a1 (@IN a0 y0 x0) (x2 y0) (@ARB a1)) (@ARB a1)) = (@COND a1 (@IN a0 y0 x1) (x2 y0) (@ARB a1)).
