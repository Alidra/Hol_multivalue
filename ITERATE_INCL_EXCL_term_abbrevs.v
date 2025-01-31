Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term289 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @iterate a1 a0 x0 (@INTER a0 x1 x2) x3.
Definition term218 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x0 x2) /\ (~ (x1 x2))) \/ ((x0 x2) /\ (x1 x2))).
Definition term182 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (x1 x2))).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 (@DIFF a0 x1 x2)) /\ (@IN a0 x0 (@INTER a0 x1 x2)).
Definition term217 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x0 x2)) \/ (x1 x2)) /\ ((~ (x0 x2)) \/ (~ (x1 x2))).
Definition term222 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((x0 x2) /\ (~ (((x0 x2) /\ (~ (x1 x2))) \/ ((x0 x2) /\ (x1 x2))))).
Definition term313 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> @FINITE a0 (@DIFF a0 x0 x1).
Definition term381 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : a0) := forall y0 : a0, (x1 x2 (x1 x0 y0)) = (x1 x0 (x1 x2 y0)).
Definition term329 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := (@monoidal a1 x1) -> ((@FINITE a0 x0) /\ ((@FINITE a0 x2) /\ (@DISJOINT a0 x0 x2))) -> (@iterate a1 a0 x1 (@UNION a0 x0 x2) x3) = (x1 (@iterate a1 a0 x1 x0 x3) (@iterate a1 a0 x1 x2 x3)).
Definition term278 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x0 x2) \/ (x1 x2)) /\ (~ ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2))))) \/ ((~ ((x0 x2) \/ (x1 x2))) /\ ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2)).
Definition term44 := (~ False) -> False.
Definition term330 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term233 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@UNION a0 x1 x2)).
Definition term280 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ((y1 y2) \/ (y0 y2)) = ((((y1 y2) /\ (~ (y0 y2))) \/ ((y0 y2) /\ (~ (y1 y2)))) \/ ((y1 y2) /\ (y0 y2))))) -> False) x0.
Definition term226 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, (y1 y2) = (((y1 y2) /\ (~ (y0 y2))) \/ ((y1 y2) /\ (y0 y2))))) -> False) x0.
Definition term190 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, (y0 y2) = (((y0 y2) /\ (~ (y1 y2))) \/ ((y1 y2) /\ (y0 y2))))) -> False) x0.
Definition term143 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ ((((y1 y2) /\ (~ (y0 y2))) \/ ((y0 y2) /\ (~ (y1 y2)))) /\ ((y1 y2) /\ (y0 y2))))) -> False) x0.
Definition term104 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y0 y2) /\ (~ (y1 y2))) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False) x0.
Definition term75 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y0 y2) /\ (~ (y1 y2))) /\ ((y1 y2) /\ (y0 y2))))) -> False) x0.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y1 y2) /\ (~ (y0 y2))) /\ ((y1 y2) /\ (y0 y2))))) -> False) x0.
Definition term269 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and (~ ((x0 x2) \/ (x1 x2))).
Definition term332 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@monoidal a1 x1) /\ ((@FINITE a0 x0) /\ ((@FINITE a0 x2) /\ (@DISJOINT a0 x0 x2)))) -> (@iterate a1 a0 x1 (@UNION a0 x0 x2) x3) = (x1 (@iterate a1 a0 x1 x0 x3) (@iterate a1 a0 x1 x2 x3)).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @INTER a0 (@DIFF a0 x1 x0) (@INTER a0 x0 x1).
Definition term362 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@DIFF a0 x1 x0)) /\ ((@FINITE a0 (@DIFF a0 x0 x1)) /\ (@DISJOINT a0 (@DIFF a0 x1 x0) (@DIFF a0 x0 x1))).
Definition term347 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@DIFF a0 x1 x0)) /\ ((@FINITE a0 (@INTER a0 x0 x1)) /\ (@DISJOINT a0 (@DIFF a0 x1 x0) (@INTER a0 x0 x1))).
Definition term375 (a0 : Type') (x0 : type1400 a0) := (forall y0 : a0, forall y1 : a0, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 (x0 y0 y1) y2) = (x0 y0 (x0 y1 y2))) /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2)))).
Definition term404 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, ((@FINITE a0 y0) /\ (@FINITE a0 y1)) -> (x0 (@iterate a1 a0 x0 y0 y2) (@iterate a1 a0 x0 y1 y2)) = (x0 (@iterate a1 a0 x0 (@UNION a0 y0 y1) y2) (@iterate a1 a0 x0 (@INTER a0 y0 y1) y2)).
Definition term320 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@FINITE a0 y2) /\ (@DISJOINT a0 y1 y2))) -> (@iterate a1 a0 x0 (@UNION a0 y1 y2) y0) = (x0 (@iterate a1 a0 x0 y1 y0) (@iterate a1 a0 x0 y2 y0)).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) = (@IN a0 y0 (@UNION a0 (@DIFF a0 x0 x1) (@INTER a0 x0 x1))).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ~ ((((y0 y1) /\ (~ (x0 y1))) \/ ((x0 y1) /\ (~ (y0 y1)))) /\ ((y0 y1) /\ (x0 y1))).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ~ (((x0 y1) /\ (~ (y0 y1))) /\ ((y0 y1) /\ (~ (x0 y1)))).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ~ (((x0 y1) /\ (~ (y0 y1))) /\ ((y0 y1) /\ (x0 y1))).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ~ (((y0 y1) /\ (~ (x0 y1))) /\ ((y0 y1) /\ (x0 y1))).
Definition term285 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @iterate a1 a0 x0 (@UNION a0 x1 x2) x3.
Definition term261 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x1 x2) /\ (~ (x0 x2)))) /\ (~ ((x0 x2) /\ (~ (x1 x2)))).
Definition term32 (x0 : Prop) := ~ (~ x0).
Definition term236 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1))) \/ (@IN a0 x0 (@INTER a0 x1 x2)).
Definition term265 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and (((~ (x1 x2)) \/ (x0 x2)) /\ ((~ (x0 x2)) \/ (x1 x2))).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) /\ ((x0 x2) /\ (x1 x2))).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x1 x2) /\ (((~ (x1 x2)) \/ (x0 x2)) /\ ((~ (x0 x2)) \/ (~ (x1 x2)))).
Definition term122 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INTER a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) (@INTER a0 x1 x2))).
Definition term83 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INTER a0 (@DIFF a0 x2 x1) (@DIFF a0 x1 x2))).
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INTER a0 (@DIFF a0 x2 x1) (@INTER a0 x1 x2))).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INTER a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2))).
Definition term244 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0)))).
Definition term201 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0)))).
Definition term156 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0)))).
Definition term259 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) \/ (x1 x2)).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (x1 x2).
Definition term268 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2))).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (~ (x1 x2)))).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ (x1 x2)).
Definition term241 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))).
Definition term305 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 x0) \/ (@FINITE a0 y0)) -> @FINITE a0 (@INTER a0 x0 y0).
Definition term318 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@UNION a0 x0 x1).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term302 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2)) x3) (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@INTER a0 x1 x2)) x3).
Definition term298 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x1 (@iterate a1 a0 x1 (@UNION a0 (@DIFF a0 x0 x2) (@INTER a0 x0 x2)) x3) (@iterate a1 a0 x1 x2 x3).
Definition term403 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> a1, ((@FINITE a0 y0) /\ (@FINITE a0 y1)) -> (x0 (@iterate a1 a0 x0 y0 y2) (@iterate a1 a0 x0 y1 y2)) = (x0 (@iterate a1 a0 x0 (@UNION a0 y0 y1) y2) (@iterate a1 a0 x0 (@INTER a0 y0 y1) y2)).
Definition term321 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@FINITE a0 y2) /\ (@DISJOINT a0 y1 y2))) -> (@iterate a1 a0 x0 (@UNION a0 y1 y2) y0) = (x0 (@iterate a1 a0 x0 y1 y0) (@iterate a1 a0 x0 y2 y0)).
Definition term256 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y1 y2) \/ (y0 y2)) = ((((y1 y2) /\ (~ (y0 y2))) \/ ((y0 y2) /\ (~ (y1 y2)))) \/ ((y1 y2) /\ (y0 y2))).
Definition term213 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) = (((y1 y2) /\ (~ (y0 y2))) \/ ((y1 y2) /\ (y0 y2))).
Definition term168 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (y0 y2) = (((y0 y2) /\ (~ (y1 y2))) \/ ((y1 y2) /\ (y0 y2))).
Definition term141 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ~ ((((y1 y2) /\ (~ (y0 y2))) \/ ((y0 y2) /\ (~ (y1 y2)))) /\ ((y1 y2) /\ (y0 y2))).
Definition term102 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ~ (((y0 y2) /\ (~ (y1 y2))) /\ ((y1 y2) /\ (~ (y0 y2)))).
Definition term73 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ~ (((y0 y2) /\ (~ (y1 y2))) /\ ((y1 y2) /\ (y0 y2))).
Definition term40 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ~ (((y1 y2) /\ (~ (y0 y2))) /\ ((y1 y2) /\ (y0 y2))).
Definition term147 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN a0 x0 x1).
Definition term366 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@DIFF a0 x1 x2)) x3).
Definition term297 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2)) x3).
Definition term288 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@UNION a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) (@INTER a0 x1 x2)) x3).
Definition term25 (x0 : Prop) := (~ x0) -> False.
Definition term354 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@DIFF a0 x1 x0)) /\ (@FINITE a0 (@DIFF a0 x0 x1)).
Definition term317 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 (@UNION a0 x0 y0)) = ((@FINITE a0 x0) /\ (@FINITE a0 y0))) x1.
Definition term195 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 (@DIFF a0 x1 x2)) \/ (@IN a0 x0 (@INTER a0 x1 x2)).
Definition term257 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (((x0 x2) \/ (x1 x2)) = ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2))))) -> False.
Definition term214 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x0 x2) = (((x0 x2) /\ (~ (x1 x2))) \/ ((x0 x2) /\ (x1 x2))))) -> False.
Definition term169 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x1 x2) = (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (x1 x2))))) -> False.
Definition term334 (a0 : Type') (x0 : type1400 a0) := and (@monoidal a0 x0).
Definition term336 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@FINITE a0 (@DIFF a0 x0 x1)).
Definition term353 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@UNION a0 (@DIFF a0 x1 x0) (@DIFF a0 x0 x1)).
Definition term361 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@DIFF a0 x0 x1)) /\ (@DISJOINT a0 (@DIFF a0 x1 x0) (@DIFF a0 x0 x1)).
Definition term284 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @iterate a1 a0 x0 (@UNION a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) (@INTER a0 x1 x2)).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 (@UNION a0 (@DIFF a0 x0 x1) (@DIFF a0 x1 x0)) (@INTER a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 (@DIFF a0 x1 x0) (@DIFF a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 (@DIFF a0 x1 x0) (@INTER a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 (@DIFF a0 x0 x1) (@INTER a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term405 (a0 : Type') (a1 : Type') := forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0 -> a1, ((@FINITE a0 y1) /\ (@FINITE a0 y2)) -> (y0 (@iterate a1 a0 y0 y1 y3) (@iterate a1 a0 y0 y2 y3)) = (y0 (@iterate a1 a0 y0 (@UNION a0 y1 y2) y3) (@iterate a1 a0 y0 (@INTER a0 y1 y2) y3)).
Definition term364 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@DIFF a0 x1 x2)) x3.
Definition term301 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@INTER a0 x1 x2)) x3.
Definition term295 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2)) x3.
Definition term187 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((x1 x2) /\ (((~ (x1 x2)) \/ (x0 x2)) /\ ((~ (x0 x2)) \/ (~ (x1 x2))))).
Definition term149 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@INTER a0 x1 x2)).
Definition term220 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ (((x0 x2) /\ (~ (x1 x2))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term235 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) (@INTER a0 x1 x2)).
Definition term192 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @UNION a0 (@DIFF a0 x0 x1) (@INTER a0 x0 x1).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term369 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (x0 (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3)) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term308 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) \/ (@FINITE a0 x1).
Definition term42 (x0 : Prop) := (~ x0) -> x0.
Definition term282 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ (@FINITE a0 x1).
Definition term383 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) := x1 x0 (x1 x2 x3).
Definition term368 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3)) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3).
Definition term401 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0 -> a1, ((@FINITE a0 x1) /\ (@FINITE a0 x2)) -> (x0 (@iterate a1 a0 x0 x1 y0) (@iterate a1 a0 x0 x2 y0)) = (x0 (@iterate a1 a0 x0 (@UNION a0 x1 x2) y0) (@iterate a1 a0 x0 (@INTER a0 x1 x2) y0)).
Definition term325 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> a1) := forall y0 : a0 -> Prop, ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ (@DISJOINT a0 x0 y0))) -> (@iterate a1 a0 x1 (@UNION a0 x0 y0) x2) = (x1 (@iterate a1 a0 x1 x0 x2) (@iterate a1 a0 x1 y0 x2)).
Definition term311 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 x0) -> @FINITE a0 (@DIFF a0 x0 y0).
Definition term335 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> (@FINITE a0 (@DIFF a0 x0 x1)) = True.
Definition term267 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((~ (x0 x2)) \/ (x1 x2)) /\ ((~ (x1 x2)) \/ (x0 x2))) /\ ((~ (x0 x2)) \/ (~ (x1 x2))).
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x1 x2).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@DIFF a0 x1 x2).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @INTER a0 (@UNION a0 (@DIFF a0 x0 x1) (@DIFF a0 x1 x0)) (@INTER a0 x0 x1).
Definition term341 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@DIFF a0 x0 x1)) /\ ((@FINITE a0 (@INTER a0 x0 x1)) /\ (@DISJOINT a0 (@DIFF a0 x0 x1) (@INTER a0 x0 x1))).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := and (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term283 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @iterate a1 a0 x0 (@UNION a0 x1 x2).
Definition term376 (a0 : Type') (x0 : type1400 a0) := (forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 (x0 y0 y1) y2) = (x0 y0 (x0 y1 y2))) /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2))).
Definition term392 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @iterate a1 a0 x0 (@DIFF a0 x1 x2) x3.
Definition term395 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3).
Definition term287 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@UNION a0 x1 x2) x3).
Definition term373 (a0 : Type') (x0 : type1400 a0) := (forall y0 : a0, (x0 (@neutral a0 x0) y0) = y0) /\ ((forall y0 : a0, (x0 y0 (@neutral a0 x0)) = y0) /\ ((forall y0 : a0, forall y1 : a0, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 (x0 y0 y1) y2) = (x0 y0 (x0 y1 y2))) /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2)))))).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((x0 x2) /\ (~ (x1 x2))).
Definition term371 (a0 : Type') (x0 : type1400 a0) := (fun y0 : type1400 a0 => (@monoidal a0 y0) -> (forall y1 : a0, (y0 (@neutral a0 y0) y1) = y1) /\ ((forall y1 : a0, (y0 y1 (@neutral a0 y0)) = y1) /\ ((forall y1 : a0, forall y2 : a0, (y0 y1 y2) = (y0 y2 y1)) /\ ((forall y1 : a0, forall y2 : a0, forall y3 : a0, (y0 (y0 y1 y2) y3) = (y0 y1 (y0 y2 y3))) /\ (forall y1 : a0, forall y2 : a0, forall y3 : a0, (y0 y1 (y0 y2 y3)) = (y0 y2 (y0 y1 y3))))))) x0.
Definition term181 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x1 x2)) \/ (x0 x2)) /\ ((~ (x0 x2)) \/ (~ (x1 x2))).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ~ ((((y0 y1) /\ (~ (x0 y1))) \/ ((x0 y1) /\ (~ (y0 y1)))) /\ ((y0 y1) /\ (x0 y1))).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ~ (((x0 y1) /\ (~ (y0 y1))) /\ ((y0 y1) /\ (~ (x0 y1)))).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ~ (((x0 y1) /\ (~ (y0 y1))) /\ ((y0 y1) /\ (x0 y1))).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ~ (((y0 y1) /\ (~ (x0 y1))) /\ ((y0 y1) /\ (x0 y1))).
Definition term112 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term307 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) \/ (@FINITE a0 x1)) -> @FINITE a0 (@INTER a0 x0 x1).
Definition term306 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 x0) \/ (@FINITE a0 y0)) -> @FINITE a0 (@INTER a0 x0 y0)) x1.
Definition term389 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) := (fun y0 : a0 => (x1 (x1 x0 x2) y0) = (x1 x0 (x1 x2 y0))) x3.
Definition term382 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) := (fun y0 : a0 => (x1 x2 (x1 x0 y0)) = (x1 x0 (x1 x2 y0))) x3.
Definition term355 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@FINITE a0 (@UNION a0 (@DIFF a0 x1 x0) (@DIFF a0 x0 x1))).
Definition term324 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ (@DISJOINT a0 y0 y1))) -> (@iterate a1 a0 x0 (@UNION a0 y0 y1) x1) = (x0 (@iterate a1 a0 x0 y0 x1) (@iterate a1 a0 x0 y1 x1))) x2.
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @INTER a0 (@DIFF a0 x1 x0) (@DIFF a0 x0 x1).
Definition term119 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := and (@IN a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@DIFF a0 x1 x2))).
Definition term400 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@FINITE a0 x1) /\ (@FINITE a0 x2)) -> (x0 (@iterate a1 a0 x0 x1 x3) (@iterate a1 a0 x0 x2 x3)) = (x0 (@iterate a1 a0 x0 (@UNION a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @UNION a0 (@DIFF a0 x1 x0) (@INTER a0 x0 x1).
Definition term114 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@DIFF a0 x1 x2)).
Definition term286 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @iterate a1 a0 x0 (@UNION a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) (@INTER a0 x1 x2)) x3.
Definition term399 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3).
Definition term365 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3).
Definition term349 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3).
Definition term343 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3).
Definition term290 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@UNION a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (~ (x0 x2))) /\ ((x0 x2) /\ (~ (x1 x2))).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (~ (x1 x2))).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (~ (x0 x2))) /\ ((x0 x2) /\ (x1 x2)).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) /\ (~ (x1 x2))) /\ ((x0 x2) /\ (x1 x2)).
Definition term279 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x0 x2) \/ (x1 x2)) /\ ((((~ (x0 x2)) \/ (x1 x2)) /\ ((~ (x1 x2)) \/ (x0 x2))) /\ ((~ (x0 x2)) \/ (~ (x1 x2))))) \/ (((~ (x0 x2)) /\ (~ (x1 x2))) /\ ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))).
Definition term245 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term202 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term264 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and (~ (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (~ (x1 x2))))).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) /\ (~ (x0 x2))) /\ ((x0 x2) /\ (~ (x1 x2)))) -> False.
Definition term360 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@monoidal a1 x0) /\ ((@FINITE a0 (@DIFF a0 x2 x1)) /\ ((@FINITE a0 (@DIFF a0 x1 x2)) /\ (@DISJOINT a0 (@DIFF a0 x2 x1) (@DIFF a0 x1 x2))))) -> (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@DIFF a0 x1 x2)) x3) = (x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3)).
Definition term352 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@monoidal a1 x0) /\ ((@FINITE a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1))) /\ ((@FINITE a0 (@INTER a0 x1 x2)) /\ (@DISJOINT a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) (@INTER a0 x1 x2))))) -> (@iterate a1 a0 x0 (@UNION a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) (@INTER a0 x1 x2)) x3) = (x0 (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)).
Definition term345 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@monoidal a1 x0) /\ ((@FINITE a0 (@DIFF a0 x2 x1)) /\ ((@FINITE a0 (@INTER a0 x1 x2)) /\ (@DISJOINT a0 (@DIFF a0 x2 x1) (@INTER a0 x1 x2))))) -> (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@INTER a0 x1 x2)) x3) = (x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)).
Definition term333 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@monoidal a1 x0) /\ ((@FINITE a0 (@DIFF a0 x1 x2)) /\ ((@FINITE a0 (@INTER a0 x1 x2)) /\ (@DISJOINT a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2))))) -> (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2)) x3) = (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)).
Definition term196 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) /\ (~ (x1 x2))) \/ ((x0 x2) /\ (x1 x2)).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (x1 x2)).
Definition term293 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x1 (@iterate a1 a0 x1 x0 x3) (@iterate a1 a0 x1 x2 x3).
Definition term250 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ((y0 y1) \/ (x0 y1)) = ((((y0 y1) /\ (~ (x0 y1))) \/ ((x0 y1) /\ (~ (y0 y1)))) \/ ((y0 y1) /\ (x0 y1))).
Definition term207 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (y0 y1) = (((y0 y1) /\ (~ (x0 y1))) \/ ((y0 y1) /\ (x0 y1))).
Definition term162 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (x0 y1) = (((x0 y1) /\ (~ (y0 y1))) \/ ((y0 y1) /\ (x0 y1))).
Definition term239 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2)).
Definition term370 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (x0 (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3)) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (((x1 x2) /\ (~ (x0 x2))) /\ ((x0 x2) /\ (x1 x2))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (((x0 x2) /\ (~ (x1 x2))) /\ ((x0 x2) /\ (x1 x2))).
Definition term242 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @DISJOINT a0 (@DIFF a0 x0 x1) (@INTER a0 x0 x1).
Definition term398 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3)) (x0 (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)).
Definition term350 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)) (x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)).
Definition term255 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, ((y1 y2) \/ (y0 y2)) = ((((y1 y2) /\ (~ (y0 y2))) \/ ((y0 y2) /\ (~ (y1 y2)))) \/ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term212 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, (y1 y2) = (((y1 y2) /\ (~ (y0 y2))) \/ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term167 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, (y0 y2) = (((y0 y2) /\ (~ (y1 y2))) \/ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term140 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ ((((y1 y2) /\ (~ (y0 y2))) \/ ((y0 y2) /\ (~ (y1 y2)))) /\ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term101 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y0 y2) /\ (~ (y1 y2))) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term72 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y0 y2) /\ (~ (y1 y2))) /\ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term39 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y1 y2) /\ (~ (y0 y2))) /\ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (~ (~ (x1 x2))).
Definition term263 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (~ (x1 x2)))).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term215 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) = (((x0 x2) /\ (~ (x1 x2))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) /\ (~ (x1 x2))).
Definition term303 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @eq a1 (x0 (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2)) x3) (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@INTER a0 x1 x2)) x3)).
Definition term340 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@INTER a0 x0 x1)) /\ (@DISJOINT a0 (@DIFF a0 x0 x1) (@INTER a0 x0 x1)).
Definition term346 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@INTER a0 x0 x1)) /\ (@DISJOINT a0 (@DIFF a0 x1 x0) (@INTER a0 x0 x1)).
Definition term327 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@FINITE a0 x0) /\ ((@FINITE a0 x2) /\ (@DISJOINT a0 x0 x2))) -> (@iterate a1 a0 x1 (@UNION a0 x0 x2) x3) = (x1 (@iterate a1 a0 x1 x0 x3) (@iterate a1 a0 x1 x2 x3)).
Definition term110 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) (@INTER a0 x1 x2)).
Definition term277 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (((x0 x2) \/ (x1 x2)) /\ ((((~ (x0 x2)) \/ (x1 x2)) /\ ((~ (x1 x2)) \/ (x0 x2))) /\ ((~ (x0 x2)) \/ (~ (x1 x2))))).
Definition term384 (a0 : Type') (x0 : type1400 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 (x0 y0 y1) y2) = (x0 y0 (x0 y1 y2)).
Definition term377 (a0 : Type') (x0 : type1400 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2)).
Definition term153 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))).
Definition term260 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) /\ (~ (x1 x2)).
Definition term339 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@FINITE a0 (@INTER a0 x0 x1)).
Definition term229 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@UNION a0 x0 x1)) = (@IN a0 y0 (@UNION a0 (@UNION a0 (@DIFF a0 x0 x1) (@DIFF a0 x1 x0)) (@INTER a0 x0 x1))).
Definition term272 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x0 x2)) /\ (~ (x1 x2))) /\ ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2))).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0)))).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0))))).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0)))).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0)))).
Definition term315 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 (@UNION a0 y0 y1)) = ((@FINITE a0 y0) /\ (@FINITE a0 y1))) x0.
Definition term310 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a0 (@DIFF a0 y0 y1)) x0.
Definition term304 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y0) \/ (@FINITE a0 y1)) -> @FINITE a0 (@INTER a0 y0 y1)) x0.
Definition term351 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @eq a1 (x0 (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)) (x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3))).
Definition term224 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) /\ (~ (((x0 x2) /\ (~ (x1 x2))) \/ ((x0 x2) /\ (x1 x2))))) \/ ((~ (x0 x2)) /\ (((x0 x2) /\ (~ (x1 x2))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term188 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (~ (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (x1 x2))))) \/ ((~ (x1 x2)) /\ (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term248 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))).
Definition term205 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))).
Definition term160 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))).
Definition term314 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@DIFF a0 x0 x1).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x1) = (@IN a0 y0 (@UNION a0 (@DIFF a0 x1 x0) (@INTER a0 x0 x1))).
Definition term243 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term200 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term294 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2)).
Definition term316 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 (@UNION a0 x0 y0)) = ((@FINITE a0 x0) /\ (@FINITE a0 y0)).
Definition term281 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, ((y0 y1) \/ (x0 y1)) = ((((y0 y1) /\ (~ (x0 y1))) \/ ((x0 y1) /\ (~ (y0 y1)))) \/ ((y0 y1) /\ (x0 y1))))) -> False) x1.
Definition term227 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, (y0 y1) = (((y0 y1) /\ (~ (x0 y1))) \/ ((y0 y1) /\ (x0 y1))))) -> False) x1.
Definition term191 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, (x0 y1) = (((x0 y1) /\ (~ (y0 y1))) \/ ((y0 y1) /\ (x0 y1))))) -> False) x1.
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ ((((y0 y1) /\ (~ (x0 y1))) \/ ((x0 y1) /\ (~ (y0 y1)))) /\ ((y0 y1) /\ (x0 y1))))) -> False) x1.
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ (((x0 y1) /\ (~ (y0 y1))) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False) x1.
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ (((x0 y1) /\ (~ (y0 y1))) /\ ((y0 y1) /\ (x0 y1))))) -> False) x1.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ (((y0 y1) /\ (~ (x0 y1))) /\ ((y0 y1) /\ (x0 y1))))) -> False) x1.
Definition term326 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ (@DISJOINT a0 x0 y0))) -> (@iterate a1 a0 x1 (@UNION a0 x0 y0) x2) = (x1 (@iterate a1 a0 x1 x0 x2) (@iterate a1 a0 x1 y0 x2))) x3.
Definition term193 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@UNION a0 (@DIFF a0 x0 x1) (@INTER a0 x0 x1))).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x1) = (@IN a0 y0 (@UNION a0 (@DIFF a0 x1 x0) (@INTER a0 x0 x1))).
Definition term328 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ (@DISJOINT a0 x0 x1)).
Definition term358 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@monoidal a1 x0) /\ ((@FINITE a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1))) /\ ((@FINITE a0 (@INTER a0 x1 x2)) /\ (@DISJOINT a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) (@INTER a0 x1 x2)))).
Definition term312 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 x0) -> @FINITE a0 (@DIFF a0 x0 y0)) x1.
Definition term228 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @UNION a0 (@UNION a0 (@DIFF a0 x0 x1) (@DIFF a0 x1 x0)) (@INTER a0 x0 x1).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((~ (x0 x2)) \/ (x1 x2)).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) /\ ((x0 x2) /\ (x1 x2)).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term203 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term158 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term131 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term251 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, ((y0 y1) \/ (x0 y1)) = ((((y0 y1) /\ (~ (x0 y1))) \/ ((x0 y1) /\ (~ (y0 y1)))) \/ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term208 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, (y0 y1) = (((y0 y1) /\ (~ (x0 y1))) \/ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term163 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, (x0 y1) = (((x0 y1) /\ (~ (y0 y1))) \/ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term136 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, ~ ((((y0 y1) /\ (~ (x0 y1))) \/ ((x0 y1) /\ (~ (y0 y1)))) /\ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term97 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, ~ (((x0 y1) /\ (~ (y0 y1))) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, ~ (((x0 y1) /\ (~ (y0 y1))) /\ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, ~ (((y0 y1) /\ (~ (x0 y1))) /\ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term331 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term299 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @eq a1 (x1 (@iterate a1 a0 x1 (@UNION a0 (@DIFF a0 x0 x2) (@INTER a0 x0 x2)) x3) (@iterate a1 a0 x1 x2 x3)).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) /\ ((x0 x2) /\ (x1 x2))).
Definition term322 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@FINITE a0 y2) /\ (@DISJOINT a0 y1 y2))) -> (@iterate a1 a0 x0 (@UNION a0 y1 y2) y0) = (x0 (@iterate a1 a0 x0 y1 y0) (@iterate a1 a0 x0 y2 y0))) x1.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @DISJOINT a0 (@DIFF a0 x1 x0) (@DIFF a0 x0 x1).
Definition term402 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, ((@FINITE a0 x1) /\ (@FINITE a0 y0)) -> (x0 (@iterate a1 a0 x0 x1 y1) (@iterate a1 a0 x0 y0 y1)) = (x0 (@iterate a1 a0 x0 (@UNION a0 x1 y0) y1) (@iterate a1 a0 x0 (@INTER a0 x1 y0) y1)).
Definition term323 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ (@DISJOINT a0 y0 y1))) -> (@iterate a1 a0 x0 (@UNION a0 y0 y1) x1) = (x0 (@iterate a1 a0 x0 y0 x1) (@iterate a1 a0 x0 y1 x1)).
Definition term225 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) /\ (((~ (x0 x2)) \/ (x1 x2)) /\ ((~ (x0 x2)) \/ (~ (x1 x2))))) \/ ((~ (x0 x2)) /\ (((x0 x2) /\ (~ (x1 x2))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (((~ (x1 x2)) \/ (x0 x2)) /\ ((~ (x0 x2)) \/ (~ (x1 x2))))) \/ ((~ (x1 x2)) /\ (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term292 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @eq a1 (x1 (@iterate a1 a0 x1 x0 x3) (@iterate a1 a0 x1 x2 x3)).
Definition term273 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((x0 x2) \/ (x1 x2)).
Definition term116 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := or (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term199 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))).
Definition term154 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))).
Definition term367 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3)).
Definition term344 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)).
Definition term309 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@INTER a0 x0 x1).
Definition term253 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ((y1 y2) \/ (y0 y2)) = ((((y1 y2) /\ (~ (y0 y2))) \/ ((y0 y2) /\ (~ (y1 y2)))) \/ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term210 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, (y1 y2) = (((y1 y2) /\ (~ (y0 y2))) \/ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term165 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, (y0 y2) = (((y0 y2) /\ (~ (y1 y2))) \/ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term138 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ ((((y1 y2) /\ (~ (y0 y2))) \/ ((y0 y2) /\ (~ (y1 y2)))) /\ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term99 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y0 y2) /\ (~ (y1 y2))) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term70 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y0 y2) /\ (~ (y1 y2))) /\ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term37 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y1 y2) /\ (~ (y0 y2))) /\ ((y1 y2) /\ (y0 y2))))) -> False.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (@IN a0 x1 x2).
Definition term232 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) \/ (x1 x2).
Definition term240 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNION a0 x0 x1)) = (@IN a0 y0 (@UNION a0 (@UNION a0 (@DIFF a0 x0 x1) (@DIFF a0 x1 x0)) (@INTER a0 x0 x1))).
Definition term271 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x0 x2) \/ (x1 x2))) /\ ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2))).
Definition term221 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (((~ (x0 x2)) \/ (x1 x2)) /\ ((~ (x0 x2)) \/ (~ (x1 x2)))).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @UNION a0 (@DIFF a0 x1 x0) (@DIFF a0 x0 x1).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INTER a0 (@UNION a0 (@DIFF a0 x0 x1) (@DIFF a0 x1 x0)) (@INTER a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INTER a0 (@DIFF a0 x1 x0) (@DIFF a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INTER a0 (@DIFF a0 x1 x0) (@INTER a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INTER a0 (@DIFF a0 x0 x1) (@INTER a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 (@DIFF a0 x2 x1)) /\ (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 (@DIFF a0 x2 x1)) /\ (@IN a0 x0 (@INTER a0 x1 x2)).
Definition term237 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := or (@IN a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@DIFF a0 x1 x2))).
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) /\ ((x0 x2) /\ (x1 x2))) -> False.
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) /\ (~ (x0 x2))) /\ ((x0 x2) /\ (x1 x2))) -> False.
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x0 x2) /\ (~ (x1 x2))) /\ ((x0 x2) /\ (x1 x2))) -> False.
Definition term296 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> a1) := x0 (@iterate a1 a0 x0 x1 x2).
Definition term356 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@INTER a0 x0 x1)) /\ (@DISJOINT a0 (@UNION a0 (@DIFF a0 x0 x1) (@DIFF a0 x1 x0)) (@INTER a0 x0 x1)).
Definition term183 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x1 x2)) /\ (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (x1 x2))).
Definition term386 (a0 : Type') (x0 : a0) (x1 : type1400 a0) := forall y0 : a0, forall y1 : a0, (x1 (x1 x0 y0) y1) = (x1 x0 (x1 y0 y1)).
Definition term379 (a0 : Type') (x0 : type1400 a0) (x1 : a0) := forall y0 : a0, forall y1 : a0, (x0 x1 (x0 y0 y1)) = (x0 y0 (x0 x1 y1)).
Definition term300 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x2 x1) (@INTER a0 x1 x2)).
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (~ (x1 x2)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @INTER a0 (@DIFF a0 x0 x1) (@INTER a0 x0 x1).
Definition term387 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : a0) := (fun y0 : a0 => forall y1 : a0, (x1 (x1 x0 y0) y1) = (x1 x0 (x1 y0 y1))) x2.
Definition term380 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => forall y1 : a0, (x0 x1 (x0 y0 y1)) = (x0 y0 (x0 x1 y1))) x2.
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (x1 x2).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (((x1 x2) /\ (~ (x0 x2))) /\ ((x0 x2) /\ (~ (x1 x2)))).
Definition term276 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (((x0 x2) \/ (x1 x2)) /\ (~ ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2))))).
Definition term270 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((~ (x0 x2)) /\ (~ (x1 x2))).
Definition term337 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) \/ (@FINITE a0 x1)) -> (@FINITE a0 (@INTER a0 x0 x1)) = True.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (~ (@IN a0 x1 x2)).
Definition term234 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((x0 x2) \/ (x1 x2)).
Definition term385 (a0 : Type') (x0 : type1400 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0, (x0 (x0 y0 y1) y2) = (x0 y0 (x0 y1 y2))) x1.
Definition term378 (a0 : Type') (x0 : type1400 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0, (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2))) x1.
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x1 x2) /\ (~ (x0 x2))) /\ ((x0 x2) /\ (~ (x1 x2)))).
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 (@DIFF a0 x2 x1) (@INTER a0 x1 x2)).
Definition term238 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (~ (x1 x2)))).
Definition term198 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))).
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x1 x2) = (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term363 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@monoidal a1 x0) /\ ((@FINITE a0 (@DIFF a0 x2 x1)) /\ ((@FINITE a0 (@DIFF a0 x1 x2)) /\ (@DISJOINT a0 (@DIFF a0 x2 x1) (@DIFF a0 x1 x2)))).
Definition term348 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@monoidal a1 x0) /\ ((@FINITE a0 (@DIFF a0 x2 x1)) /\ ((@FINITE a0 (@INTER a0 x1 x2)) /\ (@DISJOINT a0 (@DIFF a0 x2 x1) (@INTER a0 x1 x2)))).
Definition term342 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@monoidal a1 x0) /\ ((@FINITE a0 (@DIFF a0 x1 x2)) /\ ((@FINITE a0 (@INTER a0 x1 x2)) /\ (@DISJOINT a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2)))).
Definition term219 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) /\ (((x0 x2) /\ (~ (x1 x2))) \/ ((x0 x2) /\ (x1 x2))).
Definition term357 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@UNION a0 (@DIFF a0 x0 x1) (@DIFF a0 x1 x0))) /\ ((@FINITE a0 (@INTER a0 x0 x1)) /\ (@DISJOINT a0 (@UNION a0 (@DIFF a0 x0 x1) (@DIFF a0 x1 x0)) (@INTER a0 x0 x1))).
Definition term186 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((x1 x2) /\ (~ (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (x1 x2))))).
Definition term275 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) \/ (x1 x2)) /\ ((((~ (x0 x2)) \/ (x1 x2)) /\ ((~ (x1 x2)) \/ (x0 x2))) /\ ((~ (x0 x2)) \/ (~ (x1 x2)))).
Definition term374 (a0 : Type') (x0 : type1400 a0) := (forall y0 : a0, (x0 y0 (@neutral a0 x0)) = y0) /\ ((forall y0 : a0, forall y1 : a0, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 (x0 y0 y1) y2) = (x0 y0 (x0 y1 y2))) /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2))))).
Definition term319 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@FINITE a0 y2) /\ ((@FINITE a0 y3) /\ (@DISJOINT a0 y2 y3))) -> (@iterate a1 a0 y0 (@UNION a0 y2 y3) y1) = (y0 (@iterate a1 a0 y0 y2 y1) (@iterate a1 a0 y0 y3 y1))) x0.
Definition term254 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ((y1 y2) \/ (y0 y2)) = ((((y1 y2) /\ (~ (y0 y2))) \/ ((y0 y2) /\ (~ (y1 y2)))) \/ ((y1 y2) /\ (y0 y2))).
Definition term211 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) = (((y1 y2) /\ (~ (y0 y2))) \/ ((y1 y2) /\ (y0 y2))).
Definition term166 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y0 y2) = (((y0 y2) /\ (~ (y1 y2))) \/ ((y1 y2) /\ (y0 y2))).
Definition term139 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ~ ((((y1 y2) /\ (~ (y0 y2))) \/ ((y0 y2) /\ (~ (y1 y2)))) /\ ((y1 y2) /\ (y0 y2))).
Definition term100 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ~ (((y0 y2) /\ (~ (y1 y2))) /\ ((y1 y2) /\ (~ (y0 y2)))).
Definition term71 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ~ (((y0 y2) /\ (~ (y1 y2))) /\ ((y1 y2) /\ (y0 y2))).
Definition term38 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ~ (((y1 y2) /\ (~ (y0 y2))) /\ ((y1 y2) /\ (y0 y2))).
Definition term397 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := @eq a1 (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (x0 (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)))).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((x0 x2) /\ (~ (x1 x2))).
Definition term247 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> ((~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ((x0 y0) \/ (x1 y0)) = ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term204 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> ((~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x0 y0) = (((x0 y0) /\ (~ (x1 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> ((~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, (x1 y0) = (((x1 y0) /\ (~ (x0 y0))) \/ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> ((~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ ((((x0 y0) /\ (~ (x1 y0))) \/ ((x1 y0) /\ (~ (x0 y0)))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> ((~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> ((~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ (((x1 y0) /\ (~ (x0 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> ((~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False) -> (~ (forall y0 : a0, ~ (((x0 y0) /\ (~ (x1 y0))) /\ ((x0 y0) /\ (x1 y0))))) -> False.
Definition term249 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, ((y0 y1) \/ (x0 y1)) = ((((y0 y1) /\ (~ (x0 y1))) \/ ((x0 y1) /\ (~ (y0 y1)))) \/ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term206 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, (y0 y1) = (((y0 y1) /\ (~ (x0 y1))) \/ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term161 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, (x0 y1) = (((x0 y1) /\ (~ (y0 y1))) \/ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term134 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ ((((y0 y1) /\ (~ (x0 y1))) \/ ((x0 y1) /\ (~ (y0 y1)))) /\ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term95 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ (((x0 y1) /\ (~ (y0 y1))) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term66 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ (((x0 y1) /\ (~ (y0 y1))) /\ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ (((y0 y1) /\ (~ (x0 y1))) /\ ((y0 y1) /\ (x0 y1))))) -> False.
Definition term230 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (@IN a0 x0 x1).
Definition term372 (a0 : Type') (x0 : type1400 a0) := (@monoidal a0 x0) -> (forall y0 : a0, (x0 (@neutral a0 x0) y0) = y0) /\ ((forall y0 : a0, (x0 y0 (@neutral a0 x0)) = y0) /\ ((forall y0 : a0, forall y1 : a0, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 (x0 y0 y1) y2) = (x0 y0 (x0 y1 y2))) /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 y0 (x0 y1 y2)) = (x0 y1 (x0 y0 y2)))))).
Definition term396 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (x0 (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3))).
Definition term391 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@DIFF a0 x1 x2) x3) (x0 (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3) (x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3))).
Definition term390 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : a0) (x3 : a0) := x0 (x0 x1 x2) x3.
Definition term80 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 (@DIFF a0 x2 x1) (@DIFF a0 x1 x2)).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x1 x2) /\ (~ (x0 x2))) /\ ((x0 x2) /\ (x1 x2))).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x0 x2) /\ (~ (x1 x2))) /\ ((x0 x2) /\ (x1 x2))).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term111 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1))) /\ (@IN a0 x0 (@INTER a0 x1 x2)).
Definition term184 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x1 x2) /\ (~ (((x1 x2) /\ (~ (x0 x2))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and (~ ((x0 x2) /\ (~ (x1 x2)))).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) /\ (x1 x2)).
Definition term216 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x0 x2) /\ (~ (x1 x2)))) /\ (~ ((x0 x2) /\ (x1 x2))).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x1 x2) /\ (~ (x0 x2)))) /\ (~ ((x0 x2) /\ (x1 x2))).
Definition term394 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (x0 (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)).
Definition term393 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3) (x0 (@iterate a1 a0 x0 (@DIFF a0 x2 x1) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3)).
Definition term223 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((x0 x2) /\ (((~ (x0 x2)) \/ (x1 x2)) /\ ((~ (x0 x2)) \/ (~ (x1 x2))))).
Definition term388 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : a0) := forall y0 : a0, (x1 (x1 x0 x2) y0) = (x1 x0 (x1 x2 y0)).
Definition term252 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ((y0 y1) \/ (x0 y1)) = ((((y0 y1) /\ (~ (x0 y1))) \/ ((x0 y1) /\ (~ (y0 y1)))) \/ ((y0 y1) /\ (x0 y1))).
Definition term209 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (y0 y1) = (((y0 y1) /\ (~ (x0 y1))) \/ ((y0 y1) /\ (x0 y1))).
Definition term164 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (x0 y1) = (((x0 y1) /\ (~ (y0 y1))) \/ ((y0 y1) /\ (x0 y1))).
Definition term258 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x0 x2) \/ (x1 x2)) = ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term150 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 (@DIFF a0 x2 x1)) \/ (@IN a0 x0 (@INTER a0 x1 x2)).
Definition term115 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 (@DIFF a0 x2 x1)) \/ (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term359 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3).
Definition term291 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x0 (@iterate a1 a0 x0 (@UNION a0 (@UNION a0 (@DIFF a0 x1 x2) (@DIFF a0 x2 x1)) (@INTER a0 x1 x2)) x3) (@iterate a1 a0 x0 (@INTER a0 x1 x2) x3).
Definition term262 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x1 x2)) \/ (x0 x2)) /\ ((~ (x0 x2)) \/ (x1 x2)).
Definition term274 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) \/ (x1 x2)) /\ (~ ((((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2)))) \/ ((x0 x2) /\ (x1 x2)))).
Definition term338 (a0 : Type') (x0 : a0 -> Prop) := or (@FINITE a0 x0).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @DISJOINT a0 (@DIFF a0 x1 x0) (@INTER a0 x0 x1).
Definition term194 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 (@DIFF a0 x1 x2) (@INTER a0 x1 x2)).
Definition term231 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
Definition term266 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (((x0 x2) /\ (~ (x1 x2))) \/ ((x1 x2) /\ (~ (x0 x2))))) /\ (~ ((x0 x2) /\ (x1 x2))).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @DISJOINT a0 (@UNION a0 (@DIFF a0 x0 x1) (@DIFF a0 x1 x0)) (@INTER a0 x0 x1).
