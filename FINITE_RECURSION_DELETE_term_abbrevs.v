Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term63 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a1) := (@FINITE a0 x1) -> forall y0 : a0, (@ITSET a1 a0 x0 (@INSERT a0 y0 x1) x2) = (@COND a1 (@IN a0 y0 x1) (@ITSET a1 a0 x0 x1 x2) (x0 y0 (@ITSET a1 a0 x0 x1 x2))).
Definition term196 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := or ((x0 x1) /\ (~ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := or ((x0 x1) /\ (~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))))).
Definition term154 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ ((~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2))).
Definition term160 := (~ False) -> False.
Definition term56 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET a1 a0 x0 (@INSERT a0 y0 y1) x1) = (@COND a1 (@IN a0 y0 y1) (@ITSET a1 a0 x0 y1 x1) (x0 y0 (@ITSET a1 a0 x0 y1 x1)))) x2.
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) := (fun y0 : type1411 a0 a1 => forall y1 : a1, (forall y2 : a0, forall y3 : a0, forall y4 : a1, (~ (y2 = y3)) -> (y0 y2 (y0 y3 y4)) = (y0 y3 (y0 y2 y4))) -> ((@ITSET a1 a0 y0 (@EMPTY a0) y1) = y1) /\ (forall y2 : a0, forall y3 : a0 -> Prop, (@FINITE a0 y3) -> (@ITSET a1 a0 y0 (@INSERT a0 y2 y3) y1) = (@COND a1 (@IN a0 y2 y3) (@ITSET a1 a0 y0 y3 y1) (y0 y2 (@ITSET a1 a0 y0 y3 y1))))) x0.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@FINITE a0 y0) -> @FINITE a0 (@DELETE a0 y0 y1)) x0.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (@IN a0 x1 (@DELETE a0 x0 y0)) = ((@IN a0 x1 x0) /\ (~ (x1 = y0))).
Definition term184 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (~ (y0 x0)) -> forall y1 : a0, (y0 y1) = ((y0 y1) /\ (~ (y1 = x0))).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : Prop => y0 \/ (~ y0)) (@IN a0 x0 x1).
Definition term120 (x0 : Prop) := ~ (~ x0).
Definition term33 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := (fun y0 : a1 => ((@ITSET a1 a0 x0 (@EMPTY a0) y0) = y0) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@ITSET a1 a0 x0 (@INSERT a0 y1 y2) y0) = (@COND a1 (@IN a0 y1 y2) (@ITSET a1 a0 x0 y2 y0) (x0 y1 (@ITSET a1 a0 x0 y2 y0))))) x1.
Definition term207 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := (forall y0 : a1, ((@ITSET a1 a0 x0 (@EMPTY a0) y0) = y0) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@ITSET a1 a0 x0 (@INSERT a0 y1 y2) y0) = (@COND a1 (@IN a0 y1 y2) (@ITSET a1 a0 x0 y2 y0) (x0 y1 (@ITSET a1 a0 x0 y2 y0))))) -> ((@ITSET a1 a0 x0 (@EMPTY a0) x1) = x1) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET a1 a0 x0 y1 x1) = (@COND a1 (@IN a0 y0 y1) (x0 y0 (@ITSET a1 a0 x0 (@DELETE a0 y1 y0) x1)) (@ITSET a1 a0 x0 (@DELETE a0 y1 y0) x1))).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x0 x1) /\ (~ (x1 = x2))).
Definition term149 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@DELETE a0 x0 y1)) = ((@IN a0 y0 x0) /\ (~ (y0 = y1)))) x1.
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))).
Definition term203 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((~ (y1 y0)) -> forall y2 : a0, (y1 y2) = ((y1 y2) /\ (~ (y2 = y0))))) -> False) x0.
Definition term163 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((y1 y0) -> forall y2 : a0, (y1 y2) = ((y2 = y0) \/ ((y1 y2) /\ (~ (y2 = y0)))))) -> False) x0.
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := or ((x0 x1) /\ ((~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2)))).
Definition term101 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@FINITE a0 x0) -> @FINITE a0 (@DELETE a0 x0 x1).
Definition term200 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term147 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term169 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (~ (@IN a0 x0 x1)).
Definition term100 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term98 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN a0 x0 x1).
Definition term113 (x0 : Prop) := (~ x0) -> False.
Definition term209 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) := forall y0 : a1, (forall y1 : a0, forall y2 : a0, forall y3 : a1, (~ (y1 = y2)) -> (x0 y1 (x0 y2 y3)) = (x0 y2 (x0 y1 y3))) -> ((@ITSET a1 a0 x0 (@EMPTY a0) y0) = y0) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@ITSET a1 a0 x0 y2 y0) = (@COND a1 (@IN a0 y1 y2) (x0 y1 (@ITSET a1 a0 x0 (@DELETE a0 y2 y1) y0)) (@ITSET a1 a0 x0 (@DELETE a0 y2 y1) y0))).
Definition term23 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) := forall y0 : a1, (forall y1 : a0, forall y2 : a0, forall y3 : a1, (~ (y1 = y2)) -> (x0 y1 (x0 y2 y3)) = (x0 y2 (x0 y1 y3))) -> ((@ITSET a1 a0 x0 (@EMPTY a0) y0) = y0) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@ITSET a1 a0 x0 (@INSERT a0 y1 y2) y0) = (@COND a1 (@IN a0 y1 y2) (@ITSET a1 a0 x0 y2 y0) (x0 y1 (@ITSET a1 a0 x0 y2 y0)))).
Definition term156 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term191 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ ((x0 x1) = ((x0 x1) /\ (~ (x1 = x2))))) -> False.
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ ((x0 x1) = ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))))) -> False.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @IN a0 x1 (@DELETE a0 x0 x1).
Definition term66 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> forall y1 : a0, (@ITSET a1 a0 x0 (@INSERT a0 y1 y0) x1) = (@COND a1 (@IN a0 y1 y0) (@ITSET a1 a0 x0 y0 x1) (x0 y1 (@ITSET a1 a0 x0 y0 x1)))) x2.
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1))))).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @FINITE a0 (@DELETE a0 x0 x1).
Definition term64 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0, (@ITSET a1 a0 x0 (@INSERT a0 y1 y0) x1) = (@COND a1 (@IN a0 y1 y0) (@ITSET a1 a0 x0 y0 x1) (x0 y1 (@ITSET a1 a0 x0 y0 x1))).
Definition term15 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0, @FINITE a0 (@DELETE a0 y0 y1).
Definition term68 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := forall y0 : a0, (@ITSET a1 a0 x0 (@INSERT a0 y0 (@DELETE a0 x1 x2)) x3) = (@COND a1 (@IN a0 y0 (@DELETE a0 x1 x2)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3) (x0 y0 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3))).
Definition term62 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a1) := forall y0 : a0, (@ITSET a1 a0 x0 (@INSERT a0 y0 x1) x2) = (@COND a1 (@IN a0 y0 x1) (@ITSET a1 a0 x0 x1 x2) (x0 y0 (@ITSET a1 a0 x0 x1 x2))).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x1 = x2)) /\ (~ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term182 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))).
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@DELETE a0 x0 x1)).
Definition term195 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ ((~ (x0 x1)) \/ (x1 = x2)).
Definition term122 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (y0 x0) -> forall y1 : a0, (y0 y1) = ((y1 = x0) \/ ((y0 y1) /\ (~ (y1 = x0)))).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (@IN a0 x1 x0)) -> forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@DELETE a0 x0 x1)).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term158 (x0 : Prop) := (~ x0) -> x0.
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@DELETE a0 x1 x2).
Definition term35 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := @eq a1 (@ITSET a1 a0 x0 (@EMPTY a0) x1).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x0 x1) /\ ((~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2)))) \/ ((~ (x0 x1)) /\ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := (fun y0 : a1 => (forall y1 : a0, forall y2 : a0, forall y3 : a1, (~ (y1 = y2)) -> (x0 y1 (x0 y2 y3)) = (x0 y2 (x0 y1 y3))) -> ((@ITSET a1 a0 x0 (@EMPTY a0) y0) = y0) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@ITSET a1 a0 x0 (@INSERT a0 y1 y2) y0) = (@COND a1 (@IN a0 y1 y2) (@ITSET a1 a0 x0 y2 y0) (x0 y1 (@ITSET a1 a0 x0 y2 y0))))) x1.
Definition term103 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 = x2) \/ (@IN a0 x0 (@DELETE a0 x1 x2)).
Definition term194 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ (~ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term53 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @COND a1 False (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3).
Definition term44 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3.
Definition term80 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @COND a1 False (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3) (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term79 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @COND a1 False (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3).
Definition term153 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))).
Definition term165 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) := @ITSET a1 a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)).
Definition term76 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) /\ False.
Definition term187 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((~ (y1 y0)) -> forall y2 : a0, (y1 y2) = ((y1 y2) /\ (~ (y2 = y0))))) -> False.
Definition term125 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((y1 y0) -> forall y2 : a0, (y1 y2) = ((y2 = y0) \/ ((y1 y2) /\ (~ (y2 = y0)))))) -> False.
Definition term46 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @COND a1 True (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3).
Definition term60 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : a1) := @ITSET a1 a0 x0 (@INSERT a0 x1 x2) x3.
Definition term74 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term75 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term186 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (~ (y0 x0)) -> forall y1 : a0, (y0 y1) = ((y0 y1) /\ (~ (y1 = x0))).
Definition term32 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) := (fun y0 : type1411 a0 a1 => (forall y1 : a0, forall y2 : a0, forall y3 : a1, (~ (y1 = y2)) -> (y0 y1 (y0 y2 y3)) = (y0 y2 (y0 y1 y3))) -> forall y1 : a1, ((@ITSET a1 a0 y0 (@EMPTY a0) y1) = y1) /\ (forall y2 : a0, forall y3 : a0 -> Prop, (@FINITE a0 y3) -> (@ITSET a1 a0 y0 (@INSERT a0 y2 y3) y1) = (@COND a1 (@IN a0 y2 y3) (@ITSET a1 a0 y0 y3 y1) (y0 y2 (@ITSET a1 a0 y0 y3 y1))))) x0.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, @FINITE a0 (@DELETE a0 x0 y0).
Definition term47 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a1) := @eq a1 (@ITSET a1 a0 x0 x1 x2).
Definition term205 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) := @ITSET a1 a0 x0 (@DELETE a0 x1 x2).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))) -> False) -> (~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))) -> False.
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False.
Definition term85 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := ((@ITSET a1 a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)) x3) = (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3))) -> (@ITSET a1 a0 x0 x1 x3) = (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term30 (a0 : Type') (a1 : Type') := forall y0 : type1411 a0 a1, (forall y1 : a0, forall y2 : a0, forall y3 : a1, (~ (y1 = y2)) -> (y0 y1 (y0 y2 y3)) = (y0 y2 (y0 y1 y3))) -> forall y1 : a1, ((@ITSET a1 a0 y0 (@EMPTY a0) y1) = y1) /\ (forall y2 : a0, forall y3 : a0 -> Prop, (@FINITE a0 y3) -> (@ITSET a1 a0 y0 (@INSERT a0 y2 y3) y1) = (@COND a1 (@IN a0 y2 y3) (@ITSET a1 a0 y0 y3 y1) (y0 y2 (@ITSET a1 a0 y0 y3 y1)))).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) -> forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@INSERT a0 x1 (@DELETE a0 x0 x1))).
Definition term69 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a1) (x3 : a0) := (fun y0 : a0 => (@ITSET a1 a0 x0 (@INSERT a0 y0 (@DELETE a0 x1 x3)) x2) = (@COND a1 (@IN a0 y0 (@DELETE a0 x1 x3)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x3) x2) (x0 y0 (@ITSET a1 a0 x0 (@DELETE a0 x1 x3) x2)))) x3.
Definition term206 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0) (x2 : a1) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@ITSET a1 a0 x0 y0 x2) = (@COND a1 (@IN a0 x1 y0) (x0 x1 (@ITSET a1 a0 x0 (@DELETE a0 y0 x1) x2)) (@ITSET a1 a0 x0 (@DELETE a0 y0 x1) x2)).
Definition term57 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1411 a0 a1) (x2 : a1) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@ITSET a1 a0 x1 (@INSERT a0 x0 y0) x2) = (@COND a1 (@IN a0 x0 y0) (@ITSET a1 a0 x1 y0 x2) (x1 x0 (@ITSET a1 a0 x1 y0 x2))).
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> (@IN a0 x0 x1) = False.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> forall y1 : a0, @FINITE a0 (@DELETE a0 y0 y1)) x0.
Definition term86 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a1) := fun y0 : a1 => (@ITSET a1 a0 x0 x1 x2) = y0.
Definition term54 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := (@FINITE a0 x1) -> (@ITSET a1 a0 x0 x1 x3) = (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3).
Definition term82 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := imp ((@ITSET a1 a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)) x3) = (@COND a1 (@IN a0 x2 (@DELETE a0 x1 x2)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3) (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)))).
Definition term201 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term136 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (x0 = x1)).
Definition term42 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @COND a1 (@IN a0 x2 x1) (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ (~ (x1 = x2)).
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term151 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) \/ (~ (@IN a0 x0 x1)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (@IN a0 x1 (@DELETE a0 x0 y0)) = ((@IN a0 x1 x0) /\ (~ (x1 = y0)))) x2.
Definition term50 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := (@FINITE a0 x1) -> (@ITSET a1 a0 x0 x1 x3) = (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) := forall y0 : a0, forall y1 : a0, forall y2 : a1, (~ (y0 = y1)) -> (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2)).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @INSERT a0 x1 (@DELETE a0 x0 x1).
Definition term45 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @COND a1 (@IN a0 x2 x1) (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3).
Definition term39 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := True /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET a1 a0 x0 y1 x1) = (@COND a1 (@IN a0 y0 y1) (x0 y0 (@ITSET a1 a0 x0 (@DELETE a0 y1 y0) x1)) (@ITSET a1 a0 x0 (@DELETE a0 y1 y0) x1))).
Definition term71 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @COND a1 (@IN a0 x2 (@DELETE a0 x1 x2)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3) (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term192 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x0 x1) = ((x0 x1) /\ (~ (x1 = x2)))).
Definition term126 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (y1 y0) -> forall y2 : a0, (y1 y2) = ((y2 = y0) \/ ((y1 y2) /\ (~ (y2 = y0)))).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ (~ (x1 = x2)).
Definition term204 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((~ (y0 x0)) -> forall y1 : a0, (y0 y1) = ((y0 y1) /\ (~ (y1 = x0))))) -> False) x1.
Definition term164 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((y0 x0) -> forall y1 : a0, (y0 y1) = ((y1 = x0) \/ ((y0 y1) /\ (~ (y1 = x0)))))) -> False) x1.
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (@IN a0 y0 x0) = (@IN a0 y0 (@INSERT a0 x1 (@DELETE a0 x0 x1))).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@INSERT a0 x1 (@DELETE a0 x0 x1))).
Definition term83 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := imp ((@ITSET a1 a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)) x3) = (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3))).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (((~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))) -> False) -> (~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))) -> False) -> (~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))) -> False.
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (((~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False.
Definition term185 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (~ ((~ (y0 x0)) -> forall y1 : a0, (y0 y1) = ((y0 y1) /\ (~ (y1 = x0))))) -> False.
Definition term123 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (~ ((y0 x0) -> forall y1 : a0, (y0 y1) = ((y1 = x0) \/ ((y0 y1) /\ (~ (y1 = x0)))))) -> False.
Definition term94 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term152 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term105 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term107 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term167 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := (forall y0 : a0, @FINITE a0 (@DELETE a0 x1 y0)) -> (@ITSET a1 a0 x0 x1 x3) = (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term188 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (~ (y1 y0)) -> forall y2 : a0, (y1 y2) = ((y1 y2) /\ (~ (y2 = y0))).
Definition term141 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ (~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@FINITE a0 x0) -> @FINITE a0 (@DELETE a0 x0 y0).
Definition term189 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (~ ((~ (y1 y0)) -> forall y2 : a0, (y1 y2) = ((y1 y2) /\ (~ (y2 = y0))))) -> False.
Definition term127 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (~ ((y1 y0) -> forall y2 : a0, (y1 y2) = ((y2 = y0) \/ ((y1 y2) /\ (~ (y2 = y0)))))) -> False.
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) := (forall y0 : a0, forall y1 : a0, forall y2 : a1, (~ (y0 = y1)) -> (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2))) -> forall y0 : a1, ((@ITSET a1 a0 x0 (@EMPTY a0) y0) = y0) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@ITSET a1 a0 x0 (@INSERT a0 y1 y2) y0) = (@COND a1 (@IN a0 y1 y2) (@ITSET a1 a0 x0 y2 y0) (x0 y1 (@ITSET a1 a0 x0 y2 y0)))).
Definition term36 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := and ((@ITSET a1 a0 x0 (@EMPTY a0) x1) = x1).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))).
Definition term52 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @COND a1 False (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term89 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @eq Prop ((fun y0 : a1 => (@ITSET a1 a0 x0 x1 x3) = y0) (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3))).
Definition term102 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)).
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (@IN a0 x1 x0)) -> x0 = (@DELETE a0 x0 x1).
Definition term81 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @eq a1 (@ITSET a1 a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)) x3).
Definition term193 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) /\ ((x0 x1) /\ (~ (x1 = x2))).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (~ (x0 x1)).
Definition term166 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := (forall y0 : a0, (@ITSET a1 a0 x0 (@INSERT a0 y0 (@DELETE a0 x1 x2)) x3) = (@COND a1 (@IN a0 y0 (@DELETE a0 x1 x2)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3) (x0 y0 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)))) -> (@ITSET a1 a0 x0 x1 x3) = (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))).
Definition term61 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1411 a0 a1) (x2 : a0 -> Prop) (x3 : a1) := @COND a1 (@IN a0 x0 x2) (@ITSET a1 a0 x1 x2 x3) (x1 x0 (@ITSET a1 a0 x1 x2 x3)).
Definition term124 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (y0 x0) -> forall y1 : a0, (y0 y1) = ((y1 = x0) \/ ((y0 y1) /\ (~ (y1 = x0)))).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0, (@IN a0 y0 (@DELETE a0 x0 y1)) = ((@IN a0 y0 x0) /\ (~ (y0 = y1))).
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) /\ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term59 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1411 a0 a1) (x2 : a0 -> Prop) (x3 : a1) := (@FINITE a0 x2) -> (@ITSET a1 a0 x1 (@INSERT a0 x0 x2) x3) = (@COND a1 (@IN a0 x0 x2) (@ITSET a1 a0 x1 x2 x3) (x1 x0 (@ITSET a1 a0 x1 x2 x3))).
Definition term161 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => @FINITE a0 (@DELETE a0 x0 y0)) x1.
Definition term202 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => x0 y0) x1).
Definition term198 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x0 x1) /\ (~ ((x0 x1) /\ (~ (x1 = x2))))) \/ ((~ (x0 x1)) /\ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term84 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := ((@ITSET a1 a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)) x3) = (@COND a1 (@IN a0 x2 (@DELETE a0 x1 x2)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3) (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)))) -> (@ITSET a1 a0 x0 x1 x3) = (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term148 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@FINITE a0 x0) -> @FINITE a0 (@DELETE a0 x0 y0)) x1.
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (~ (~ (x1 = x2))).
Definition term78 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @COND a1 (@IN a0 x2 (@DELETE a0 x1 x2)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3).
Definition term70 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @ITSET a1 a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)) x3.
Definition term88 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := (fun y0 : a1 => (@ITSET a1 a0 x0 x1 x3) = y0) (@ITSET a1 a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)) x3).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := or ((x0 x1) /\ ((~ (x0 x1)) \/ (x1 = x2))).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (@IN a0 y0 x0) = (@IN a0 y0 (@DELETE a0 x0 x1)).
Definition term67 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := (@FINITE a0 (@DELETE a0 x1 x2)) -> forall y0 : a0, (@ITSET a1 a0 x0 (@INSERT a0 y0 (@DELETE a0 x1 x2)) x3) = (@COND a1 (@IN a0 y0 (@DELETE a0 x1 x2)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3) (x0 y0 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3))).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x0 x1) /\ (~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))))) \/ ((~ (x0 x1)) /\ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> forall y0 : a0, @FINITE a0 (@DELETE a0 x0 y0).
Definition term31 (a0 : Type') (a1 : Type') := (forall y0 : type1411 a0 a1, forall y1 : a1, (forall y2 : a0, forall y3 : a0, forall y4 : a1, (~ (y2 = y3)) -> (y0 y2 (y0 y3 y4)) = (y0 y3 (y0 y2 y4))) -> ((@ITSET a1 a0 y0 (@EMPTY a0) y1) = y1) /\ (forall y2 : a0, forall y3 : a0 -> Prop, (@FINITE a0 y3) -> (@ITSET a1 a0 y0 (@INSERT a0 y2 y3) y1) = (@COND a1 (@IN a0 y2 y3) (@ITSET a1 a0 y0 y3 y1) (y0 y2 (@ITSET a1 a0 y0 y3 y1))))) -> forall y0 : type1411 a0 a1, (forall y1 : a0, forall y2 : a0, forall y3 : a1, (~ (y1 = y2)) -> (y0 y1 (y0 y2 y3)) = (y0 y2 (y0 y1 y3))) -> forall y1 : a1, ((@ITSET a1 a0 y0 (@EMPTY a0) y1) = y1) /\ (forall y2 : a0, forall y3 : a0 -> Prop, (@FINITE a0 y3) -> (@ITSET a1 a0 y0 (@INSERT a0 y2 y3) y1) = (@COND a1 (@IN a0 y2 y3) (@ITSET a1 a0 y0 y3 y1) (y0 y2 (@ITSET a1 a0 y0 y3 y1)))).
Definition term16 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0, (@FINITE a0 y0) -> @FINITE a0 (@DELETE a0 y0 y1)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0, @FINITE a0 (@DELETE a0 y0 y1).
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x0 x1) = ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1)))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0, (@IN a0 y1 (@DELETE a0 y0 y2)) = ((@IN a0 y1 y0) /\ (~ (y1 = y2)))) x0.
Definition term181 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (((~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))) -> False) -> (~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))) -> False) -> ((~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))) -> False) -> (~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))) -> False.
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (((~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> ((~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False.
Definition term77 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0) := @COND a1 (@IN a0 x1 (@DELETE a0 x0 x1)).
Definition term183 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (~ ((~ (y0 x0)) -> forall y1 : a0, (y0 y1) = ((y0 y1) /\ (~ (y1 = x0))))) -> False.
Definition term121 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (~ ((y0 x0) -> forall y1 : a0, (y0 y1) = ((y1 = x0) \/ ((y0 y1) /\ (~ (y1 = x0)))))) -> False.
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ ((~ (x0 x1)) -> forall y0 : a0, (x0 y0) = ((x0 y0) /\ (~ (y0 = x1))))) -> False.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False.
Definition term87 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := (fun y0 : a1 => (@ITSET a1 a0 x0 x1 x3) = y0) (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) := forall y0 : a1, ((@ITSET a1 a0 x0 (@EMPTY a0) y0) = y0) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@ITSET a1 a0 x0 (@INSERT a0 y1 y2) y0) = (@COND a1 (@IN a0 y1 y2) (@ITSET a1 a0 x0 y2 y0) (x0 y1 (@ITSET a1 a0 x0 y2 y0)))).
Definition term58 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1411 a0 a1) (x2 : a1) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@ITSET a1 a0 x1 (@INSERT a0 x0 y0) x2) = (@COND a1 (@IN a0 x0 y0) (@ITSET a1 a0 x1 y0 x2) (x1 x0 (@ITSET a1 a0 x1 y0 x2)))) x3.
Definition term41 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3).
Definition term90 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @eq Prop ((@ITSET a1 a0 x0 x1 x3) = (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3))).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (x1 = x2).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) /\ (~ (x1 = x1)).
Definition term208 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := (forall y0 : a0, forall y1 : a0, forall y2 : a1, (~ (y0 = y1)) -> (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2))) -> ((@ITSET a1 a0 x0 (@EMPTY a0) x1) = x1) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET a1 a0 x0 y1 x1) = (@COND a1 (@IN a0 y0 y1) (x0 y0 (@ITSET a1 a0 x0 (@DELETE a0 y1 y0) x1)) (@ITSET a1 a0 x0 (@DELETE a0 y1 y0) x1))).
Definition term25 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := (forall y0 : a0, forall y1 : a0, forall y2 : a1, (~ (y0 = y1)) -> (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2))) -> ((@ITSET a1 a0 x0 (@EMPTY a0) x1) = x1) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET a1 a0 x0 (@INSERT a0 y0 y1) x1) = (@COND a1 (@IN a0 y0 y1) (@ITSET a1 a0 x0 y1 x1) (x0 y0 (@ITSET a1 a0 x0 y1 x1)))).
Definition term199 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x0 x1) /\ ((~ (x0 x1)) \/ (x1 = x2))) \/ ((~ (x0 x1)) /\ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) -> x0 = (@INSERT a0 x1 (@DELETE a0 x0 x1)).
Definition term190 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (~ (y1 y0)) -> forall y2 : a0, (y1 y2) = ((y1 y2) /\ (~ (y2 = y0))).
Definition term128 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (y1 y0) -> forall y2 : a0, (y1 y2) = ((y2 = y0) \/ ((y1 y2) /\ (~ (y2 = y0)))).
Definition term37 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET a1 a0 x0 y1 x1) = (@COND a1 (@IN a0 y0 y1) (x0 y0 (@ITSET a1 a0 x0 (@DELETE a0 y1 y0) x1)) (@ITSET a1 a0 x0 (@DELETE a0 y1 y0) x1)).
Definition term34 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET a1 a0 x0 (@INSERT a0 y0 y1) x1) = (@COND a1 (@IN a0 y0 y1) (@ITSET a1 a0 x0 y1 x1) (x0 y0 (@ITSET a1 a0 x0 y1 x1))).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term162 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term49 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := (@FINITE a0 x1) -> (@ITSET a1 a0 x0 x1 x3) = (@COND a1 (@IN a0 x2 x1) (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)) (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term65 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET a1 a0 x0 (@INSERT a0 y0 y1) x1) = (@COND a1 (@IN a0 y0 y1) (@ITSET a1 a0 x0 y1 x1) (x0 y0 (@ITSET a1 a0 x0 y1 x1)))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0, (@ITSET a1 a0 x0 (@INSERT a0 y1 y0) x1) = (@COND a1 (@IN a0 y1 y0) (@ITSET a1 a0 x0 y0 x1) (x0 y1 (@ITSET a1 a0 x0 y0 x1))).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))).
Definition term210 (a0 : Type') (a1 : Type') := forall y0 : type1411 a0 a1, forall y1 : a1, (forall y2 : a0, forall y3 : a0, forall y4 : a1, (~ (y2 = y3)) -> (y0 y2 (y0 y3 y4)) = (y0 y3 (y0 y2 y4))) -> ((@ITSET a1 a0 y0 (@EMPTY a0) y1) = y1) /\ (forall y2 : a0, forall y3 : a0 -> Prop, (@FINITE a0 y3) -> (@ITSET a1 a0 y0 y3 y1) = (@COND a1 (@IN a0 y2 y3) (y0 y2 (@ITSET a1 a0 y0 (@DELETE a0 y3 y2) y1)) (@ITSET a1 a0 y0 (@DELETE a0 y3 y2) y1))).
Definition term21 (a0 : Type') (a1 : Type') := forall y0 : type1411 a0 a1, forall y1 : a1, (forall y2 : a0, forall y3 : a0, forall y4 : a1, (~ (y2 = y3)) -> (y0 y2 (y0 y3 y4)) = (y0 y3 (y0 y2 y4))) -> ((@ITSET a1 a0 y0 (@EMPTY a0) y1) = y1) /\ (forall y2 : a0, forall y3 : a0 -> Prop, (@FINITE a0 y3) -> (@ITSET a1 a0 y0 (@INSERT a0 y2 y3) y1) = (@COND a1 (@IN a0 y2 y3) (@ITSET a1 a0 y0 y3 y1) (y0 y2 (@ITSET a1 a0 y0 y3 y1)))).
Definition term7 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@FINITE a0 y0) -> @FINITE a0 (@DELETE a0 y0 y1).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND a1 (@IN a0 x0 x1).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2)).
Definition term131 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term43 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @COND a1 True (x0 x2 (@ITSET a1 a0 x0 (@DELETE a0 x1 x2) x3)).
Definition term150 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x0.
Definition term38 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := ((@ITSET a1 a0 x0 (@EMPTY a0) x1) = x1) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET a1 a0 x0 y1 x1) = (@COND a1 (@IN a0 y0 y1) (x0 y0 (@ITSET a1 a0 x0 (@DELETE a0 y1 y0) x1)) (@ITSET a1 a0 x0 (@DELETE a0 y1 y0) x1))).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) := ((@ITSET a1 a0 x0 (@EMPTY a0) x1) = x1) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET a1 a0 x0 (@INSERT a0 y0 y1) x1) = (@COND a1 (@IN a0 y0 y1) (@ITSET a1 a0 x0 y1 x1) (x0 y0 (@ITSET a1 a0 x0 y1 x1)))).
