Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term298 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0 -> Prop, (forall y3 : a0, (y2 y3) -> (y3 = y1) \/ (y0 y3)) -> forall y3 : a0, ((y2 y3) /\ (~ (y3 = y1))) -> y0 y3.
Definition term297 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0 -> Prop, (~ ((forall y3 : a0, (y2 y3) -> (y3 = y1) \/ (y0 y3)) -> forall y3 : a0, ((y2 y3) /\ (~ (y3 = y1))) -> y0 y3)) -> False.
Definition term436 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x1 x0)) /\ (~ (~ (x1 x2))).
Definition term267 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0).
Definition term139 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (~ (@FINITE a0 y0)) \/ (@FINITE a0 (@INSERT a0 x0 y0)).
Definition term123 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1).
Definition term408 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> x1 y0.
Definition term385 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term77 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1.
Definition term49 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 y1 y0)) -> @FINITE a0 y1.
Definition term40 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term303 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (~ (x0 x3)) \/ ((x3 = x1) \/ (x2 x3)).
Definition term182 (a0 : Type') (x0 : a0 -> Prop) := ~ (@SUBSET a0 x0 (@EMPTY a0)).
Definition term224 (a0 : Type') := (~ (@FINITE a0 (@EMPTY a0))) -> @FINITE a0 (@EMPTY a0).
Definition term129 (a0 : Type') (x0 : type686 a0) := ~ (all x0).
Definition term23 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, forall y2 : a1, y0 y1 y2) = (forall y1 : a1, forall y2 : a0, y0 y2 y1)) x0.
Definition term169 (a0 : Type') := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (~ (@SUBSET a0 y1 (@EMPTY a0))) \/ (y1 = (@EMPTY a0))) y0.
Definition term242 := (~ False) -> False.
Definition term52 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term382 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) /\ (~ (x1 x2))) \/ (((~ (x2 = x0)) /\ ((~ (x1 x2)) \/ (x2 = x0))) /\ (x1 x2)).
Definition term10 (a0 : Type') := (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1)) -> forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1).
Definition term98 (a0 : Type') := (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) -> forall y2 : a0 -> Prop, (@SUBSET a0 y2 (@INSERT a0 y0 y1)) -> @FINITE a0 y2).
Definition term330 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((forall y1 : a0, (y0 y1) -> (y1 = x0) \/ (x1 y1)) -> forall y1 : a0, ((y0 y1) /\ (~ (y1 = x0))) -> x1 y1)) -> False) x2.
Definition term243 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := @SUBSET a0 x0 (@INSERT a0 x1 x2).
Definition term104 (a0 : Type') := ((forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) -> forall y2 : a0 -> Prop, (@SUBSET a0 y2 (@INSERT a0 y0 y1)) -> @FINITE a0 y2)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1.
Definition term79 (a0 : Type') := forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0.
Definition term368 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term375 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => fun y2 : a0 -> Prop => ((@FINITE a0 y2) /\ (@SUBSET a0 y1 y2)) -> @FINITE a0 y1) y0 x0.
Definition term65 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term230 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (x1 = x0)) \/ (~ (@FINITE a0 x1)).
Definition term0 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : Prop => y0 \/ (~ y0)) (@IN a0 x0 x1).
Definition term189 (x0 : Prop) := ~ (~ x0).
Definition term152 (a0 : Type') := fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@EMPTY a0)) \/ (~ (y0 = (@EMPTY a0))).
Definition term312 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) \/ (~ (x1 x2)).
Definition term337 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (@FINITE a0 (@INSERT a0 x1 (@DELETE a0 x0 x1))).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) -> @FINITE a0 y0.
Definition term266 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> (y0 = x1) \/ (x2 y0).
Definition term326 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) -> x0 = x1.
Definition term443 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) \/ (~ (x1 x2)).
Definition term371 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x0 x1) /\ (~ (x1 = x2))).
Definition term389 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term308 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> ~ (x0 x1).
Definition term262 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) \/ (x1 x2).
Definition term248 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (@SUBSET a0 (@DELETE a0 x1 x2) x0) -> @FINITE a0 (@DELETE a0 x1 x2).
Definition term222 (a0 : Type') (x0 : a0 -> Prop) := (~ ((@EMPTY a0) = x0)) -> (@EMPTY a0) = x0.
Definition term200 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (x0 = x1).
Definition term377 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and ((~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2))).
Definition term260 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term122 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0).
Definition term212 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term322 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ (x1 x2)).
Definition term334 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 -> Prop => @FINITE a0 y0) (@INSERT a0 x1 (@DELETE a0 x0 x1)).
Definition term440 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := imp ((~ (x1 x0)) /\ (x1 x2)).
Definition term302 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term316 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((x0 x3) \/ ((x3 = x1) \/ (~ (x2 x3)))).
Definition term401 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (~ (@IN a0 x0 x1)).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> (@SUBSET a0 x1 x0) -> @FINITE a0 x1.
Definition term171 (a0 : Type') := forall y0 : a0 -> Prop, (~ (@SUBSET a0 y0 (@EMPTY a0))) \/ (y0 = (@EMPTY a0)).
Definition term254 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@DELETE a0 x0 x1)) -> @IN a0 y0 x2.
Definition term429 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (~ (y1 y2)) -> (forall y3 : a0, (y1 y3) -> (y3 = y2) \/ (y0 y3)) -> forall y3 : a0, (y1 y3) -> y0 y3.
Definition term428 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (~ ((~ (y1 y2)) -> (forall y3 : a0, (y1 y3) -> (y3 = y2) \/ (y0 y3)) -> forall y3 : a0, (y1 y3) -> y0 y3)) -> False.
Definition term314 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (x0 x3) \/ ((x3 = x1) \/ (~ (x2 x3))).
Definition term259 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term105 (x0 : Prop) := (~ x0) -> False.
Definition term347 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INSERT a0 x0 (@DELETE a0 x1 x0))) = (@IN a0 y0 x1).
Definition term39 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 -> Prop => ((@FINITE a0 y3) /\ (@SUBSET a0 y2 y3)) -> @FINITE a0 y2) y0 y1.
Definition term310 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (x3 = x0) \/ ((~ (x1 x3)) \/ (x2 x3)).
Definition term217 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term387 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term412 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)) -> False.
Definition term327 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) -> False.
Definition term357 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (~ ((x0 y0) -> forall y1 : a0, ((y1 = y0) \/ ((x0 y1) /\ (~ (y1 = y0)))) = (x0 y1))) -> False.
Definition term225 (a0 : Type') := ~ (@FINITE a0 (@EMPTY a0)).
Definition term360 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> forall y1 : a0, ((y1 = y0) \/ ((x0 y1) /\ (~ (y1 = y0)))) = (x0 y1).
Definition term268 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := imp (forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)).
Definition term252 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := imp (forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 (@INSERT a0 x1 x2)).
Definition term107 (a0 : Type') := ~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0).
Definition term331 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @FINITE a0 (@DELETE a0 x0 x1).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1)) -> @FINITE a0 (@INSERT a0 x0 x1).
Definition term450 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (~ ((~ (y1 y2)) -> (forall y3 : a0, (y1 y3) -> (y3 = y2) \/ (y0 y3)) -> forall y3 : a0, (y1 y3) -> y0 y3)) -> False) x0.
Definition term59 (a0 : Type') (x0 : Prop) (x1 : type686 a0) := x0 -> forall y0 : a0 -> Prop, x1 y0.
Definition term188 (a0 : Type') (x0 : a0 -> Prop) := (~ (~ (@SUBSET a0 x0 (@EMPTY a0)))) -> x0 = (@EMPTY a0).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> @FINITE a0 x1.
Definition term75 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1.
Definition term321 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (~ (x0 x1))).
Definition term373 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x1 = x2)) /\ (~ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term187 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term247 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> @FINITE a0 y0) -> forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> @FINITE a0 y0.
Definition term88 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (forall y0 : a0 -> Prop, (@SUBSET a0 y0 x1) -> @FINITE a0 y0) -> forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@INSERT a0 x0 x1)) -> @FINITE a0 y0.
Definition term29 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 -> Prop => ((@FINITE a0 y3) /\ (@SUBSET a0 y2 y3)) -> @FINITE a0 y2) y1 y0.
Definition term28 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 -> Prop => ((@FINITE a0 y3) /\ (@SUBSET a0 y2 y3)) -> @FINITE a0 y2) y0 y1.
Definition term27 (a0 : Type') (x0 : type639 a0) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, x0 y1 y0.
Definition term26 (a0 : Type') (x0 : type639 a0) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, x0 y0 y1.
Definition term55 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 x0) -> (@SUBSET a0 y0 x0) -> @FINITE a0 y0.
Definition term320 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term172 (a0 : Type') := (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) \/ (~ (y0 = (@EMPTY a0)))) /\ (forall y0 : a0 -> Prop, (~ (@SUBSET a0 y0 (@EMPTY a0))) \/ (y0 = (@EMPTY a0))).
Definition term126 (a0 : Type') := fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0.
Definition term163 (a0 : Type') := @eq Prop (forall y0 : a0 -> Prop, ((@SUBSET a0 y0 (@EMPTY a0)) \/ (~ (y0 = (@EMPTY a0)))) /\ ((~ (@SUBSET a0 y0 (@EMPTY a0))) \/ (y0 = (@EMPTY a0)))).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0 -> Prop, (@FINITE a0 x0) -> (@SUBSET a0 y0 x0) -> @FINITE a0 y0).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) -> @FINITE a0 y0) x1.
Definition term115 (a0 : Type') := ~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) -> @FINITE a0 y1) y0.
Definition term20 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1)) x1.
Definition term275 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := imp (@IN a0 x0 (@DELETE a0 x1 x2)).
Definition term380 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or (((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) /\ (~ (x1 x2))).
Definition term346 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := @eq Prop ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term338 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, forall y1 : a1, x0 y0 y1.
Definition term127 (a0 : Type') (x0 : a0 -> Prop) := ~ ((@SUBSET a0 x0 (@EMPTY a0)) -> @FINITE a0 x0).
Definition term155 (a0 : Type') (x0 : a0 -> Prop) := (@SUBSET a0 x0 (@EMPTY a0)) \/ (~ (x0 = (@EMPTY a0))).
Definition term183 (x0 : Prop) := (~ x0) -> x0.
Definition term216 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (x1 = x0) /\ (x1 = x2).
Definition term269 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@DELETE a0 x1 x2).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 x0) /\ (@SUBSET a0 y0 x0)) -> @FINITE a0 y0.
Definition term198 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term255 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@SUBSET a0 x0 (@INSERT a0 x1 x2)) -> @SUBSET a0 (@DELETE a0 x0 x1) x2.
Definition term156 (a0 : Type') (x0 : a0 -> Prop) := and ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@EMPTY a0)) \/ (~ (y0 = (@EMPTY a0)))) x0).
Definition term168 (a0 : Type') := and (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) \/ (~ (y0 = (@EMPTY a0)))).
Definition term215 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (x0 = x1).
Definition term93 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => forall y3 : a0 -> Prop, (@SUBSET a0 y3 y2) -> @FINITE a0 y3) y1) -> (fun y2 : a0 -> Prop => forall y3 : a0 -> Prop, (@SUBSET a0 y3 y2) -> @FINITE a0 y3) (@INSERT a0 y0 y1).
Definition term343 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 = x2) \/ (@IN a0 x0 (@DELETE a0 x1 x2)).
Definition term208 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term81 (a0 : Type') := and (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0).
Definition term110 (a0 : Type') := (~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False.
Definition term210 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term449 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := imp (~ ((~ (x0 x1)) \/ (x1 = x2))).
Definition term120 (a0 : Type') := (~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> ~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))).
Definition term205 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term5 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0).
Definition term56 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 y0) -> (@SUBSET a0 y1 y0) -> @FINITE a0 y1.
Definition term144 (a0 : Type') := fun y0 : a0 -> Prop => ((@SUBSET a0 y0 (@EMPTY a0)) \/ (~ (y0 = (@EMPTY a0)))) /\ ((~ (@SUBSET a0 y0 (@EMPTY a0))) \/ (y0 = (@EMPTY a0))).
Definition term206 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term147 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term378 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0))))) /\ (x1 x2).
Definition term226 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) \/ ((~ (x1 = x0)) \/ (~ (@FINITE a0 x1))).
Definition term384 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term356 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))).
Definition term235 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (~ ((~ (x1 = x0)) \/ (~ (@FINITE a0 x1)))).
Definition term350 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0).
Definition term203 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term420 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ ((~ (x0 y0)) -> (forall y1 : a0, (x0 y1) -> (y1 = y0) \/ (x1 y1)) -> forall y1 : a0, (x0 y1) -> x1 y1)) -> False.
Definition term359 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (~ ((x0 y0) -> forall y1 : a0, ((y1 = y0) \/ ((x0 y1) /\ (~ (y1 = y0)))) = (x0 y1))) -> False.
Definition term379 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x2 = x0)) /\ ((~ (x1 x2)) \/ (x2 = x0))) /\ (x1 x2).
Definition term433 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2))).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> @FINITE a0 (@INSERT a0 x0 x1).
Definition term21 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 -> x1 y0.
Definition term84 (a0 : Type') (x0 : a0 -> Prop) := imp (forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> @FINITE a0 y0).
Definition term293 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((forall y2 : a0, (y1 y2) -> (y2 = y0) \/ (x0 y2)) -> forall y2 : a0, ((y1 y2) /\ (~ (y2 = y0))) -> x0 y2)) -> False.
Definition term18 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (forall y2 : a0, y0 -> y1 y2) = (y0 -> forall y2 : a0, y1 y2)) x0.
Definition term223 (a0 : Type') (x0 : a0 -> Prop) := ~ ((@EMPTY a0) = x0).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (x1 = x0)) \/ ((@FINITE a0 x0) \/ (~ (@FINITE a0 x1))).
Definition term166 (a0 : Type') := forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) \/ (~ (y0 = (@EMPTY a0))).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term304 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := fun y0 : a0 => (~ (x0 y0)) \/ ((y0 = x1) \/ (x2 y0)).
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1).
Definition term229 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((~ (x0 = x1)) \/ (~ (@FINITE a0 x0)))) -> @FINITE a0 x1.
Definition term128 (a0 : Type') (x0 : a0 -> Prop) := (@SUBSET a0 x0 (@EMPTY a0)) /\ (~ (@FINITE a0 x0)).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0) x0).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term76 (a0 : Type') := (((fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => forall y3 : a0 -> Prop, (@SUBSET a0 y3 y2) -> @FINITE a0 y3) y1) -> (fun y2 : a0 -> Prop => forall y3 : a0 -> Prop, (@SUBSET a0 y3 y2) -> @FINITE a0 y3) (@INSERT a0 y0 y1))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) y0.
Definition term164 (a0 : Type') := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@EMPTY a0)) \/ (~ (y1 = (@EMPTY a0)))) y0.
Definition term220 (a0 : Type') (x0 : a0 -> Prop) := (x0 = (@EMPTY a0)) /\ (x0 = x0).
Definition term441 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((~ (x0 x2)) /\ (x0 x1)) -> ~ (x1 = x2).
Definition term116 (a0 : Type') := imp ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))).
Definition term424 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (~ ((~ (y0 y1)) -> (forall y2 : a0, (y0 y2) -> (y2 = y1) \/ (x0 y2)) -> forall y2 : a0, (y0 y2) -> x0 y2)) -> False.
Definition term363 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (~ ((y0 y1) -> forall y2 : a0, ((y2 = y1) \/ ((y0 y2) /\ (~ (y2 = y1)))) = (y0 y2))) -> False.
Definition term391 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term400 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (forall y0 : a0, (@IN a0 y0 x1) -> @IN a0 y0 (@INSERT a0 x0 x2)) -> forall y0 : a0, (@IN a0 y0 x1) -> @IN a0 y0 x2.
Definition term256 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 (@INSERT a0 x1 x2)) -> forall y0 : a0, (@IN a0 y0 (@DELETE a0 x0 x1)) -> @IN a0 y0 x2.
Definition term271 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term161 (a0 : Type') := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@EMPTY a0)) \/ (~ (y1 = (@EMPTY a0)))) y0) /\ ((fun y1 : a0 -> Prop => (~ (@SUBSET a0 y1 (@EMPTY a0))) \/ (y1 = (@EMPTY a0))) y0).
Definition term446 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (~ ((~ (x0 x3)) \/ (x3 = x1))) -> x2 x3.
Definition term434 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ ((x0 x2) \/ (~ (x0 x1)))) -> ~ (x1 = x2).
Definition term121 (a0 : Type') := fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0)).
Definition term383 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) /\ (~ (x1 x2)).
Definition term87 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) x1) -> (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) (@INSERT a0 x0 x1).
Definition term97 (a0 : Type') := ((fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => forall y3 : a0 -> Prop, (@SUBSET a0 y3 y2) -> @FINITE a0 y3) y1) -> (fun y2 : a0 -> Prop => forall y3 : a0 -> Prop, (@SUBSET a0 y3 y2) -> @FINITE a0 y3) (@INSERT a0 y0 y1)).
Definition term345 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (@IN a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2))).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term315 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((~ (x0 x3)) \/ ((x3 = x1) \/ (x2 x3))).
Definition term301 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> False.
Definition term131 (a0 : Type') := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@EMPTY a0)) -> @FINITE a0 y1) y0).
Definition term22 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 -> forall y0 : a0, x1 y0.
Definition term74 (a0 : Type') := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => fun y2 : a0 -> Prop => ((@FINITE a0 y2) /\ (@SUBSET a0 y1 y2)) -> @FINITE a0 y1) y0 x0.
Definition term193 (a0 : Type') (x0 : a0 -> Prop) := (@SUBSET a0 x0 (@EMPTY a0)) -> x0 = (@EMPTY a0).
Definition term414 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)) -> False) -> (~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)) -> False.
Definition term353 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False.
Definition term285 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := ((~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)) -> False) -> (~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)) -> False.
Definition term124 (a0 : Type') := and (@FINITE a0 (@EMPTY a0)).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> @FINITE a0 y0) -> @FINITE a0 x1.
Definition term292 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, (y0 y1) -> (y1 = x0) \/ (x1 y1)) -> forall y1 : a0, ((y0 y1) /\ (~ (y1 = x0))) -> x1 y1.
Definition term92 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 (@INSERT a0 x0 y0)) -> @FINITE a0 y1.
Definition term100 (a0 : Type') := imp ((forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) -> forall y2 : a0 -> Prop, (@SUBSET a0 y2 (@INSERT a0 y0 y1)) -> @FINITE a0 y2)).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) := and ((@SUBSET a0 x0 (@EMPTY a0)) \/ (~ (x0 = (@EMPTY a0)))).
Definition term231 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((~ (x1 = x0)) \/ (~ (@FINITE a0 x1))).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) -> @FINITE a0 y1) y0.
Definition term89 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) y0) -> (fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) (@INSERT a0 x0 y0).
Definition term365 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) = (x1 x2))) -> False.
Definition term111 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False) -> (~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False.
Definition term234 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (x1 = x0) /\ (@FINITE a0 x1).
Definition term423 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (~ (y0 y1)) -> (forall y2 : a0, (y0 y2) -> (y2 = y1) \/ (x0 y2)) -> forall y2 : a0, (y0 y2) -> x0 y2.
Definition term209 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term430 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) = (x1 x0)) -> (x1 x0) \/ (~ (x1 x2)).
Definition term349 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0).
Definition term184 (a0 : Type') (x0 : a0 -> Prop) := (x0 = (@EMPTY a0)) \/ (~ (@SUBSET a0 x0 (@EMPTY a0))).
Definition term170 (a0 : Type') := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (~ (@SUBSET a0 y1 (@EMPTY a0))) \/ (y1 = (@EMPTY a0))) y0.
Definition term165 (a0 : Type') := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@EMPTY a0)) \/ (~ (y1 = (@EMPTY a0)))) y0.
Definition term71 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) -> @FINITE a0 y1) y0.
Definition term407 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term134 (a0 : Type') := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@EMPTY a0)) -> @FINITE a0 y1) y0).
Definition term372 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (x0 = x1)).
Definition term250 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 (@INSERT a0 x1 x2).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> @FINITE a0 y0.
Definition term263 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) (x3 : a0 -> Prop) := (@IN a0 x1 x0) -> @IN a0 x1 (@INSERT a0 x2 x3).
Definition term240 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) -> @FINITE a0 x0.
Definition term272 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) := ~ (x0 = x0).
Definition term25 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a1, forall y1 : a0, x0 y1 y0.
Definition term270 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ (~ (x1 = x2)).
Definition term392 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term386 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) \/ (~ (@IN a0 x0 x1)).
Definition term237 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((x0 = x1) /\ (@FINITE a0 x0)) -> @FINITE a0 x1.
Definition term132 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0) x0.
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) \/ (~ (@FINITE a0 x1)).
Definition term80 (a0 : Type') := and ((fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) (@EMPTY a0)).
Definition term145 (a0 : Type') := forall y0 : a0 -> Prop, ((@SUBSET a0 y0 (@EMPTY a0)) \/ (~ (y0 = (@EMPTY a0)))) /\ ((~ (@SUBSET a0 y0 (@EMPTY a0))) \/ (y0 = (@EMPTY a0))).
Definition term140 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (~ (@FINITE a0 y1)) \/ (@FINITE a0 (@INSERT a0 y0 y1)).
Definition term284 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := ~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0).
Definition term318 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((~ (x0 x2)) \/ (x1 x2)).
Definition term195 (a0 : Type') (x0 : a0 -> Prop) := ~ (x0 = (@EMPTY a0)).
Definition term108 (a0 : Type') := forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0)).
Definition term190 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (@SUBSET a0 x0 (@EMPTY a0))).
Definition term332 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @INSERT a0 x1 (@DELETE a0 x0 x1).
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x1) = (@FINITE a0 x0)) -> (@FINITE a0 x0) \/ (~ (@FINITE a0 x1)).
Definition term227 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((~ (x1 = x0)) \/ ((@FINITE a0 x0) \/ (~ (@FINITE a0 x1)))).
Definition term313 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (x3 = x0) \/ ((x1 x3) \/ (~ (x2 x3))).
Definition term114 (a0 : Type') := (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False.
Definition term160 (a0 : Type') (x0 : a0 -> Prop) := ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@EMPTY a0)) \/ (~ (y0 = (@EMPTY a0)))) x0) /\ ((fun y0 : a0 -> Prop => (~ (@SUBSET a0 y0 (@EMPTY a0))) \/ (y0 = (@EMPTY a0))) x0).
Definition term306 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (~ (x0 y0)) \/ ((y0 = x1) \/ (x2 y0))) x3.
Definition term118 (a0 : Type') := ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> ~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) x0.
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @FINITE a0 (@INSERT a0 x0 x1).
Definition term13 (a0 : Type') (x0 : type686 a0) := ((x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (x0 y1) -> x0 (@INSERT a0 y0 y1))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => fun y2 : a0 -> Prop => ((@FINITE a0 y2) /\ (@SUBSET a0 y1 y2)) -> @FINITE a0 y1) x0 y0.
Definition term239 (a0 : Type') (x0 : a0 -> Prop) := (((@EMPTY a0) = x0) /\ (@FINITE a0 (@EMPTY a0))) -> @FINITE a0 x0.
Definition term274 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ (~ (x1 = x2)).
Definition term358 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> forall y1 : a0, ((y1 = y0) \/ ((x0 y1) /\ (~ (y1 = y0)))) = (x0 y1).
Definition term341 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 (@DELETE a0 x1 x0))) = (@IN a0 y0 x1).
Definition term279 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@DELETE a0 x0 x1)) -> @IN a0 y0 x2.
Definition term438 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x1 x0)) /\ (x1 x2).
Definition term150 (a0 : Type') := forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@EMPTY a0)) \/ (~ (y1 = (@EMPTY a0)))) y0) /\ ((fun y1 : a0 -> Prop => (~ (@SUBSET a0 y1 (@EMPTY a0))) \/ (y1 = (@EMPTY a0))) y0).
Definition term102 (a0 : Type') := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) y0.
Definition term106 (a0 : Type') := (~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> False.
Definition term30 (a0 : Type') := fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term335 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => @FINITE a0 y0) x0.
Definition term162 (a0 : Type') := @eq Prop (forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@EMPTY a0)) \/ (~ (y1 = (@EMPTY a0)))) y0) /\ ((fun y1 : a0 -> Prop => (~ (@SUBSET a0 y1 (@EMPTY a0))) \/ (y1 = (@EMPTY a0))) y0)).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0 -> Prop, (@FINITE a0 x0) -> (fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) -> @FINITE a0 y1) y0).
Definition term221 (a0 : Type') (x0 : a0 -> Prop) := ((x0 = (@EMPTY a0)) /\ (x0 = x0)) -> (@EMPTY a0) = x0.
Definition term245 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@FINITE a0 (@DELETE a0 x0 x1)) -> @FINITE a0 (@INSERT a0 x1 (@DELETE a0 x0 x1)).
Definition term137 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ (@FINITE a0 (@INSERT a0 x0 x1)).
Definition term340 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> (@INSERT a0 x0 (@DELETE a0 x1 x0)) = x1.
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0)) x1.
Definition term403 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> (forall y0 : a0, (@IN a0 y0 x1) -> @IN a0 y0 (@INSERT a0 x0 x2)) -> forall y0 : a0, (@IN a0 y0 x1) -> @IN a0 y0 x2.
Definition term447 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((~ (x0 x1)) \/ (x1 = x2)).
Definition term202 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) := ((@SUBSET a0 x0 (@EMPTY a0)) \/ (~ (x0 = (@EMPTY a0)))) /\ ((~ (@SUBSET a0 x0 (@EMPTY a0))) \/ (x0 = (@EMPTY a0))).
Definition term241 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> False.
Definition term204 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term113 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False) -> (~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False) -> ((~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False) -> (~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False.
Definition term415 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (((~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)) -> False) -> (~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)) -> False) -> (~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)) -> False.
Definition term354 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False.
Definition term286 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (((~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)) -> False) -> (~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)) -> False) -> (~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)) -> False.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> @FINITE a0 y0.
Definition term291 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ ((forall y1 : a0, (y0 y1) -> (y1 = x0) \/ (x1 y1)) -> forall y1 : a0, ((y0 y1) /\ (~ (y1 = x0))) -> x1 y1)) -> False.
Definition term244 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @FINITE a0 (@INSERT a0 x1 (@DELETE a0 x0 x1)).
Definition term138 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) \/ (@FINITE a0 (@INSERT a0 x0 y0)).
Definition term51 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term257 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term393 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term214 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (~ (~ (x0 = x1))).
Definition term273 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term261 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term11 (a0 : Type') := forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (y0 y2) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term411 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0.
Definition term57 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@FINITE a0 y0) -> (@SUBSET a0 y1 y0) -> @FINITE a0 y1.
Definition term50 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 y1 y0)) -> @FINITE a0 y1.
Definition term41 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term288 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := ~ (~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)).
Definition term130 (a0 : Type') (x0 : type686 a0) := exists y0 : a0 -> Prop, ~ (x0 y0).
Definition term232 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (~ (x1 = x0))) /\ (~ (~ (@FINITE a0 x1))).
Definition term410 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0.
Definition term282 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0.
Definition term295 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0 -> Prop, (~ ((forall y2 : a0, (y1 y2) -> (y2 = y0) \/ (x0 y2)) -> forall y2 : a0, ((y1 y2) /\ (~ (y2 = y0))) -> x0 y2)) -> False.
Definition term207 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term453 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@SUBSET a0 x2 (@INSERT a0 x0 x1)) -> @FINITE a0 x2.
Definition term281 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0.
Definition term329 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((forall y2 : a0, (y1 y2) -> (y2 = y0) \/ (x0 y2)) -> forall y2 : a0, ((y1 y2) /\ (~ (y2 = y0))) -> x0 y2)) -> False) x1.
Definition term174 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term333 (a0 : Type') := fun y0 : a0 -> Prop => @FINITE a0 y0.
Definition term431 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x1 x0) \/ (~ (x1 x2)).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((~ (@SUBSET a0 x0 (@EMPTY a0))) \/ (x0 = (@EMPTY a0))).
Definition term418 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ ((~ (x0 y0)) -> (forall y1 : a0, (x0 y1) -> (y1 = y0) \/ (x1 y1)) -> forall y1 : a0, (x0 y1) -> x1 y1)) -> False.
Definition term136 (a0 : Type') := exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) /\ (~ (@FINITE a0 y0)).
Definition term348 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0).
Definition term258 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term12 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (y0 y2) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) x0.
Definition term294 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0 -> Prop, (forall y2 : a0, (y1 y2) -> (y2 = y0) \/ (x0 y2)) -> forall y2 : a0, ((y1 y2) /\ (~ (y2 = y0))) -> x0 y2.
Definition term94 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) -> forall y2 : a0 -> Prop, (@SUBSET a0 y2 (@INSERT a0 y0 y1)) -> @FINITE a0 y2.
Definition term276 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := imp ((x0 x1) /\ (~ (x1 = x2))).
Definition term153 (a0 : Type') := fun y0 : a0 -> Prop => (~ (@SUBSET a0 y0 (@EMPTY a0))) \/ (y0 = (@EMPTY a0)).
Definition term58 (a0 : Type') (x0 : Prop) (x1 : type686 a0) := forall y0 : a0 -> Prop, x0 -> x1 y0.
Definition term238 (a0 : Type') (x0 : a0 -> Prop) := ((@EMPTY a0) = x0) /\ (@FINITE a0 (@EMPTY a0)).
Definition term135 (a0 : Type') := fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@EMPTY a0)) /\ (~ (@FINITE a0 y0)).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> (fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) -> @FINITE a0 y0) x1.
Definition term432 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) -> (x1 x0) \/ (~ (x1 x2)).
Definition term305 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := forall y0 : a0, (~ (x0 y0)) \/ ((y0 = x1) \/ (x2 y0)).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) := imp ((fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) x0).
Definition term342 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)).
Definition term148 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (x0 y0) /\ (x1 y0).
Definition term290 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (forall y1 : a0, (y0 y1) -> (y1 = x0) \/ (x1 y1)) -> forall y1 : a0, ((y0 y1) /\ (~ (y1 = x0))) -> x1 y1.
Definition term90 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 (@INSERT a0 x0 y0)) -> @FINITE a0 y1.
Definition term397 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (~ ((y0 y1) -> forall y2 : a0, ((y2 = y1) \/ ((y0 y2) /\ (~ (y2 = y1)))) = (y0 y2))) -> False) x0.
Definition term280 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := fun y0 : a0 => ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => fun y2 : a0 -> Prop => ((@FINITE a0 y2) /\ (@SUBSET a0 y1 y2)) -> @FINITE a0 y1) x0 y0.
Definition term398 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (~ ((x0 y0) -> forall y1 : a0, ((y1 = y0) \/ ((x0 y1) /\ (~ (y1 = y0)))) = (x0 y1))) -> False) x1.
Definition term78 (a0 : Type') := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) (@EMPTY a0).
Definition term191 (a0 : Type') (x0 : a0 -> Prop) := imp (~ (~ (@SUBSET a0 x0 (@EMPTY a0)))).
Definition term404 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (~ (x0 x1)).
Definition term406 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) -> x1 x2.
Definition term236 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((x1 = x0) /\ (@FINITE a0 x1)).
Definition term253 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := @SUBSET a0 (@DELETE a0 x0 x1) x2.
Definition term376 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and (~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term15 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term4 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1)) x0.
Definition term324 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := imp ((x0 x2) /\ (~ (x1 x2))).
Definition term399 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@SUBSET a0 x1 (@INSERT a0 x0 x2)) -> @SUBSET a0 x1 x2.
Definition term317 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := (~ ((~ (x0 x2)) \/ (x1 x2))) -> x2 = x3.
Definition term181 (a0 : Type') (x0 : a0 -> Prop) := (~ (@SUBSET a0 x0 (@EMPTY a0))) -> @SUBSET a0 x0 (@EMPTY a0).
Definition term395 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term402 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> (@SUBSET a0 x1 (@INSERT a0 x0 x2)) -> @SUBSET a0 x1 x2.
Definition term211 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term86 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@INSERT a0 x0 x1)) -> @FINITE a0 y0.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 x0) /\ (@SUBSET a0 y0 x0)) -> @FINITE a0 y0.
Definition term311 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (x1 x2).
Definition term319 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (x0 x2))) /\ (~ (x1 x2)).
Definition term196 (a0 : Type') (x0 : a0 -> Prop) := (~ (x0 = x0)) -> x0 = x0.
Definition term151 (a0 : Type') := (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@EMPTY a0)) \/ (~ (y1 = (@EMPTY a0)))) y0) /\ (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (~ (@SUBSET a0 y1 (@EMPTY a0))) \/ (y1 = (@EMPTY a0))) y0).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@FINITE a0 x0) -> (fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) -> @FINITE a0 y1) y0.
Definition term228 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((@FINITE a0 x0) \/ ((~ (x1 = x0)) \/ (~ (@FINITE a0 x1)))).
Definition term442 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) -> ~ (x0 = x1).
Definition term16 (a0 : Type') (x0 : type686 a0) := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (y0 y2) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term233 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (@FINITE a0 x0)).
Definition term178 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term388 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term421 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ (x0 y0)) -> (forall y1 : a0, (x0 y1) -> (y1 = y0) \/ (x1 y1)) -> forall y1 : a0, (x0 y1) -> x1 y1.
Definition term394 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term336 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 -> Prop => @FINITE a0 y0) (@INSERT a0 x1 (@DELETE a0 x0 x1))).
Definition term369 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (~ (~ (x1 = x2))).
Definition term154 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@EMPTY a0)) \/ (~ (y0 = (@EMPTY a0)))) x0.
Definition term422 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (~ ((~ (y0 y1)) -> (forall y2 : a0, (y0 y2) -> (y2 = y1) \/ (x0 y2)) -> forall y2 : a0, (y0 y2) -> x0 y2)) -> False.
Definition term361 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (~ ((y0 y1) -> forall y2 : a0, ((y2 = y1) \/ ((y0 y2) /\ (~ (y2 = y1)))) = (y0 y2))) -> False.
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) (@INSERT a0 x0 x1).
Definition term452 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (~ ((~ (x0 y0)) -> (forall y1 : a0, (x0 y1) -> (y1 = y0) \/ (x1 y1)) -> forall y1 : a0, (x0 y1) -> x1 y1)) -> False) x2.
Definition term265 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN a0 y0 (@INSERT a0 x1 x2).
Definition term362 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (y0 y1) -> forall y2 : a0, ((y2 = y1) \/ ((y0 y2) /\ (~ (y2 = y1)))) = (y0 y2).
Definition term249 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0 x1.
Definition term219 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term277 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) (x3 : a0 -> Prop) := (@IN a0 x2 (@DELETE a0 x0 x1)) -> @IN a0 x2 x3.
Definition term199 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term381 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) /\ (~ (x1 x2))) \/ ((~ ((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0))))) /\ (x1 x2)).
Definition term413 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0).
Definition term300 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, forall y2 : a0 -> Prop, (forall y3 : a0, (y2 y3) -> (y3 = y1) \/ (y0 y3)) -> forall y3 : a0, ((y2 y3) /\ (~ (y3 = y1))) -> y0 y3.
Definition term299 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, forall y2 : a0 -> Prop, (~ ((forall y3 : a0, (y2 y3) -> (y3 = y1) \/ (y0 y3)) -> forall y3 : a0, ((y2 y3) /\ (~ (y3 = y1))) -> y0 y3)) -> False.
Definition term167 (a0 : Type') := and (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@EMPTY a0)) \/ (~ (y1 = (@EMPTY a0)))) y0).
Definition term218 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term409 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x1 y0.
Definition term194 (a0 : Type') (x0 : a0 -> Prop) := (~ (x0 = (@EMPTY a0))) -> x0 = (@EMPTY a0).
Definition term451 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (~ ((~ (y0 y1)) -> (forall y2 : a0, (y0 y2) -> (y2 = y1) \/ (x0 y2)) -> forall y2 : a0, (y0 y2) -> x0 y2)) -> False) x1.
Definition term427 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (~ (y1 y2)) -> (forall y3 : a0, (y1 y3) -> (y3 = y2) \/ (y0 y3)) -> forall y3 : a0, (y1 y3) -> y0 y3.
Definition term426 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (~ ((~ (y1 y2)) -> (forall y3 : a0, (y1 y3) -> (y3 = y2) \/ (y0 y3)) -> forall y3 : a0, (y1 y3) -> y0 y3)) -> False.
Definition term325 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := ((x0 x2) /\ (~ (x1 x2))) -> x2 = x3.
Definition term328 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0 -> Prop, (~ ((forall y3 : a0, (y2 y3) -> (y3 = y1) \/ (y0 y3)) -> forall y3 : a0, ((y2 y3) /\ (~ (y3 = y1))) -> y0 y3)) -> False) x0.
Definition term416 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (((~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)) -> False) -> (~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)) -> False) -> ((~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)) -> False) -> (~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)) -> False.
Definition term355 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> ((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False.
Definition term287 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (((~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)) -> False) -> (~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)) -> False) -> ((~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)) -> False) -> (~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)) -> False.
Definition term339 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 (@DELETE a0 x1 x0))) = (@IN a0 y0 x1).
Definition term186 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((x0 = (@EMPTY a0)) \/ (~ (@SUBSET a0 x0 (@EMPTY a0)))).
Definition term289 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ ((forall y1 : a0, (y0 y1) -> (y1 = x0) \/ (x1 y1)) -> forall y1 : a0, ((y0 y1) /\ (~ (y1 = x0))) -> x1 y1)) -> False.
Definition term405 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) -> @IN a0 x1 x2.
Definition term439 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := imp (~ ((x1 x0) \/ (~ (x1 x2)))).
Definition term17 (a0 : Type') := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (y0 y2) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (y0 y2) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term43 (a0 : Type') := @eq Prop (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0).
Definition term42 (a0 : Type') := @eq Prop (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 -> Prop => ((@FINITE a0 y3) /\ (@SUBSET a0 y2 y3)) -> @FINITE a0 y2) y0 y1).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) := (~ (@SUBSET a0 x0 (@EMPTY a0))) \/ (x0 = (@EMPTY a0)).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) := (@SUBSET a0 x0 (@EMPTY a0)) -> @FINITE a0 x0.
Definition term351 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False.
Definition term283 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (~ ((forall y0 : a0, (x0 y0) -> (y0 = x1) \/ (x2 y0)) -> forall y0 : a0, ((x0 y0) /\ (~ (y0 = x1))) -> x2 y0)) -> False.
Definition term445 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := (x0 x2) \/ ((~ (x1 x2)) \/ (x2 = x3)).
Definition term352 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0)).
Definition term101 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) x0.
Definition term213 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (x0 = x1)).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (@SUBSET a0 y0 (@EMPTY a0))) \/ (y0 = (@EMPTY a0))) x0.
Definition term417 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ (~ ((~ (x1 x0)) -> (forall y0 : a0, (x1 y0) -> (y0 = x0) \/ (x2 y0)) -> forall y0 : a0, (x1 y0) -> x2 y0)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0) x1.
Definition term201 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ (x0 = x1)).
Definition term370 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (x1 = x2).
Definition term48 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 -> Prop => ((@FINITE a0 y3) /\ (@SUBSET a0 y2 y3)) -> @FINITE a0 y2) y1 y0.
Definition term419 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (x0 y0)) -> (forall y1 : a0, (x0 y1) -> (y1 = y0) \/ (x1 y1)) -> forall y1 : a0, (x0 y1) -> x1 y1.
Definition term278 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := ((x0 x3) /\ (~ (x3 = x1))) -> x2 x3.
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (x1 = x0) -> (@FINITE a0 x0) \/ (~ (@FINITE a0 x1)).
Definition term14 (a0 : Type') (x0 : type686 a0) := (x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (x0 y1) -> x0 (@INSERT a0 y0 y1)).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@FINITE a0 x0) -> (@SUBSET a0 y0 x0) -> @FINITE a0 y0.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term296 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0 -> Prop, (forall y2 : a0, (y1 y2) -> (y2 = y0) \/ (x0 y2)) -> forall y2 : a0, ((y1 y2) /\ (~ (y2 = y0))) -> x0 y2.
Definition term141 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (~ (@FINITE a0 y1)) \/ (@FINITE a0 (@INSERT a0 y0 y1)).
Definition term96 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) -> forall y2 : a0 -> Prop, (@SUBSET a0 y2 (@INSERT a0 y0 y1)) -> @FINITE a0 y2.
Definition term95 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => forall y3 : a0 -> Prop, (@SUBSET a0 y3 y2) -> @FINITE a0 y3) y1) -> (fun y2 : a0 -> Prop => forall y3 : a0 -> Prop, (@SUBSET a0 y3 y2) -> @FINITE a0 y3) (@INSERT a0 y0 y1).
Definition term3 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1).
Definition term264 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (x0 x3) -> (x3 = x1) \/ (x2 x3).
Definition term437 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (x0 x1)).
Definition term307 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term99 (a0 : Type') := imp (((fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => forall y3 : a0 -> Prop, (@SUBSET a0 y3 y2) -> @FINITE a0 y3) y1) -> (fun y2 : a0 -> Prop => forall y3 : a0 -> Prop, (@SUBSET a0 y3 y2) -> @FINITE a0 y3) (@INSERT a0 y0 y1))).
Definition term192 (a0 : Type') (x0 : a0 -> Prop) := imp (@SUBSET a0 x0 (@EMPTY a0)).
Definition term448 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (~ (x0 x1))) /\ (~ (x1 = x2)).
Definition term396 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term91 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) y0) -> (fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) (@INSERT a0 x0 y0).
Definition term142 (a0 : Type') := (@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (~ (@FINITE a0 y1)) \/ (@FINITE a0 (@INSERT a0 y0 y1))).
Definition term109 (a0 : Type') := (@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1)).
Definition term344 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))).
Definition term425 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (~ (y0 y1)) -> (forall y2 : a0, (y0 y2) -> (y2 = y1) \/ (x0 y2)) -> forall y2 : a0, (y0 y2) -> x0 y2.
Definition term364 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (y0 y1) -> forall y2 : a0, ((y2 = y1) \/ ((y0 y2) /\ (~ (y2 = y1)))) = (y0 y2).
Definition term103 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, (@SUBSET a0 y2 y1) -> @FINITE a0 y2) y0.
Definition term60 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 x0) -> (fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) -> @FINITE a0 y1) y0.
Definition term251 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := imp (@SUBSET a0 x0 (@INSERT a0 x1 x2)).
Definition term374 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2)).
Definition term149 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (forall y0 : a0 -> Prop, x0 y0) /\ (forall y0 : a0 -> Prop, x1 y0).
Definition term435 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x1 x0) \/ (~ (x1 x2))).
Definition term367 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term117 (a0 : Type') := ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False.
Definition term366 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) = (x1 x2)).
Definition term119 (a0 : Type') := imp (~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)).
Definition term309 (x0 : Prop) := x0 -> ~ x0.
Definition term323 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := imp (~ ((~ (x0 x2)) \/ (x1 x2))).
Definition term390 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x0.
Definition term444 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x1 x0) -> @FINITE a0 x1.
Definition term112 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False) -> (~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False) -> (~ (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) -> @FINITE a0 y0)) -> ((@FINITE a0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1))) -> (forall y0 : a0 -> Prop, (@SUBSET a0 y0 (@EMPTY a0)) = (y0 = (@EMPTY a0))) -> False.
