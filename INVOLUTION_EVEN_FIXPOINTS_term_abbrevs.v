Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term162 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ (~ ((x2 y0) = y0))) x3).
Definition term63 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ (~ (x2 y0))) x3).
Definition term428 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := (~ ((x0 (x0 x1)) = x1)) -> (x0 (x0 x1)) = x1.
Definition term407 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (@I (a0 -> Prop) x0 x2)) \/ (@I (a0 -> Prop) x0 (x1 x2)).
Definition term356 (a0 : Type') (x0 : a0 -> a0) := fun y0 : a0 -> Prop => ((forall y1 : a0, (y0 y1) -> (y0 (x0 y1)) /\ ((x0 (x0 y1)) = y1)) /\ (@FINITE a0 y0)) -> forall y1 : a0, ((y0 y1) /\ (~ ((x0 y1) = y1))) -> ((y0 (x0 y1)) /\ (~ ((x0 (x0 y1)) = (x0 y1)))) /\ ((~ ((x0 y1) = y1)) /\ ((x0 (x0 y1)) = y1)).
Definition term43 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (x2 x3)) x3.
Definition term450 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term205 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (x0 x2)) \/ ((x1 x2) = x2).
Definition term220 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := (~ ((x0 x1) = x1)) -> (x0 x1) = x1.
Definition term272 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1)).
Definition term271 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => ~ ((x1 y2) = y2)) y1)) y1)).
Definition term255 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)).
Definition term254 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => (x1 y2) = y2) y1)) y1)).
Definition term230 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1)).
Definition term4 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> (@IN a0 (x0 y0) x1) /\ ((~ ((x0 y0) = y0)) /\ ((x0 (x0 y0)) = y0)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 x1).
Definition term379 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ((x0 x1) = x1) \/ (~ ((x0 (x0 x1)) = x1)).
Definition term104 := (~ False) -> False.
Definition term429 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term222 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a0, (~ (forall y2 : a0, (((y0 y2) /\ ((y1 y2) = y2)) \/ ((y0 y2) /\ (~ ((y1 y2) = y2)))) = (y0 y2))) -> False) x0.
Definition term106 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y1 y2) /\ (y0 y2)) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False) x0.
Definition term218 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := ((((x1 x2) /\ ((x0 x2) = x2)) \/ ((x1 x2) /\ (~ ((x0 x2) = x2)))) /\ (~ (x1 x2))) \/ ((((~ (x1 x2)) \/ (~ ((x0 x2) = x2))) /\ ((~ (x1 x2)) \/ ((x0 x2) = x2))) /\ (x1 x2)).
Definition term386 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := and (@I (a0 -> Prop) x0 (x1 x2)).
Definition term12 (a0 : Type') := (forall y0 : a0 -> a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> (@IN a0 (y0 y2) y1) /\ ((~ ((y0 y2) = y2)) /\ ((y0 (y0 y2)) = y2)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y1)) -> forall y0 : a0 -> Prop, (exists y1 : a0 -> a0, (@FINITE a0 y0) /\ (forall y2 : a0, (@IN a0 y2 y0) -> (@IN a0 (y1 y2) y0) /\ ((~ ((y1 y2) = y2)) /\ ((y1 (y1 y2)) = y2)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y0).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term319 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0).
Definition term115 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((x1 = x0) /\ (x0 = y0)) -> x1 = y0) x2.
Definition term203 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ~ (((y0 y1) /\ (x0 y1)) /\ ((y0 y1) /\ (~ (x0 y1)))).
Definition term258 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term382 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := or ((~ (x0 (x1 x2))) \/ ((x1 (x1 x2)) = (x1 x2))).
Definition term316 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@IN a0 x2 x0) -> (@IN a0 (x1 x2) x0) /\ ((x1 (x1 x2)) = x2).
Definition term425 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (((x0 (x0 x2)) = x2) \/ (~ (@I (a0 -> Prop) x1 x2))).
Definition term24 (x0 : Prop) := ~ (~ x0).
Definition term329 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) /\ (~ ((x1 y0) = y0))) (x1 x2).
Definition term141 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ ((x2 y0) = y0)) x3).
Definition term462 (a0 : Type') (x0 : a0 -> a0) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> (@IN a0 (x0 y1) y0) /\ ((x0 (x0 y1)) = y1))) -> (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ ((x0 y2) = y2)) y2)))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y0)).
Definition term301 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @eq Prop (((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)))) = ((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1)))))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))))).
Definition term313 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := x0 (x0 x1).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := Coq.Arith.PeanoNat.Nat.Even (@CARD a0 x0).
Definition term414 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (~ (@I (a0 -> Prop) x0 x2))) -> @I (a0 -> Prop) x0 (x1 x2).
Definition term422 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := (~ ((x0 (x0 x1)) = (x0 x1))) -> (x0 (x0 x1)) = (x0 x1).
Definition term264 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@IN a0 x2 x0) /\ ((fun y0 : a0 => ~ ((x1 y0) = y0)) x2).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @UNION a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1)).
Definition term456 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := exists y0 : a0 -> a0, (@FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) /\ (forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((x1 y3) = y3))) y3))) -> (@IN a0 (y0 y1) (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((x1 y3) = y3))) y3))) /\ ((~ ((y0 y1) = y1)) /\ ((y0 (y0 y1)) = y1))).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (x1 x2).
Definition term348 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := ((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term347 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := ((forall y0 : a0, (@IN a0 y0 x0) -> (@IN a0 (x1 y0) x0) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) -> (@IN a0 (x1 y0) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term443 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> a0, (@FINITE a0 x0) /\ (forall y1 : a0, (@IN a0 y1 x0) -> (@IN a0 (y0 y1) x0) /\ ((~ ((y0 y1) = y1)) /\ ((y0 (y0 y1)) = y1))).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ (x1 x2)).
Definition term263 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := (fun y0 : a0 => ~ ((x0 y0) = y0)) x1.
Definition term235 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ ((@INTER a0 x0 x1) = (@EMPTY a0))).
Definition term215 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := (((~ (x1 x2)) \/ (~ ((x0 x2) = x2))) /\ ((~ (x1 x2)) \/ ((x0 x2) = x2))) /\ (x1 x2).
Definition term17 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = (y0 = x0)) = x0) x1.
Definition term383 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ ((x0 (x1 x2)) /\ (~ ((x1 (x1 x2)) = (x1 x2))))) \/ (~ ((~ ((x1 x2) = x2)) /\ ((x1 (x1 x2)) = x2))).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term385 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := @I (a0 -> Prop) x0 (x1 x2).
Definition term284 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((fun y1 : a0 => (x2 y1) = y1) y0))) y0.
Definition term167 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((x2 y0) = y0))) y0.
Definition term68 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ (x2 y0))) y0.
Definition term168 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y0) y0.
Definition term147 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ ((x2 y1) = y1)) y0) y0.
Definition term69 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ (~ (x2 y1))) y0) y0.
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ (x2 y1)) y0) y0.
Definition term197 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a0, forall y2 : a0, (((y0 y2) /\ ((y1 y2) = y2)) \/ ((y0 y2) /\ (~ ((y1 y2) = y2)))) = (y0 y2).
Definition term100 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ~ (((y1 y2) /\ (y0 y2)) /\ ((y1 y2) /\ (~ (y0 y2)))).
Definition term424 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := @eq Prop ((~ (@I (a0 -> Prop) x0 x2)) \/ ((x1 (x1 x2)) = x2)).
Definition term16 (x0 : Prop) := fun y0 : Prop => (y0 = (y0 = x0)) = x0.
Definition term281 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@IN a0 x2 x0) /\ (~ ((fun y0 : a0 => (x1 y0) = y0) x2)).
Definition term86 (x0 : Prop) := (~ x0) -> False.
Definition term333 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @eq Prop (@IN a0 (x2 x0) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y1))).
Definition term332 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @eq Prop (@IN a0 (x2 x0) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (~ ((x2 y2) = y2))) y1) y1))).
Definition term181 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNION a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ ((x0 y2) = y2)) y2)) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (~ ((x0 y2) = y2))) y2)))) = (@IN a0 y0 x1).
Definition term448 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term305 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := True /\ (forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) -> (@IN a0 (x1 y0) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0))).
Definition term372 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (x0 (x1 x2))) \/ (~ (~ ((x1 (x1 x2)) = (x1 x2)))).
Definition term228 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 x0) -> @FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (y0 y2)) y2))) x1.
Definition term402 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ((~ (@I (a0 -> Prop) x0 (x1 x2))) \/ ((x1 (x1 x2)) = (x1 x2))) \/ (((x1 x2) = x2) \/ (~ ((x1 (x1 x2)) = x2))).
Definition term384 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ((~ (x0 (x1 x2))) \/ ((x1 (x1 x2)) = (x1 x2))) \/ (((x1 x2) = x2) \/ (~ ((x1 (x1 x2)) = x2))).
Definition term363 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (((x0 (x1 x2)) /\ (~ ((x1 (x1 x2)) = (x1 x2)))) /\ ((~ ((x1 x2) = x2)) /\ ((x1 (x1 x2)) = x2)))) -> False.
Definition term410 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := (@I (a0 -> Prop) x1 (x0 x2)) \/ (~ (@I (a0 -> Prop) x1 x2)).
Definition term190 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a0 => (~ (forall y1 : a0, (((x0 y1) /\ ((y0 y1) = y1)) \/ ((x0 y1) /\ (~ ((y0 y1) = y1)))) = (x0 y1))) -> False.
Definition term451 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ((x0 (x0 x1)) = (x0 x1)) /\ ((x0 (x0 x1)) = x1).
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (x2 x3)).
Definition term354 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := ~ (~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))).
Definition term291 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) /\ ((@INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) = (@EMPTY a0)).
Definition term345 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term118 (x0 : Prop) (x1 : Prop) := (forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, ((y0 = y1) /\ (y1 = y2)) -> y0 = y2) -> x0 = x1.
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (x1 y2)) y2)) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (x1 y2))) y2)))) = (@IN a0 y0 (@EMPTY a0)).
Definition term403 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ((~ (@I (a0 -> Prop) x0 x2)) \/ (@I (a0 -> Prop) x0 (x1 x2))) /\ ((~ (@I (a0 -> Prop) x0 x2)) \/ ((x1 (x1 x2)) = x2)).
Definition term310 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := x0 (x1 x2).
Definition term344 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) -> (@IN a0 (x1 y0) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term374 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ~ ((x0 (x1 x2)) /\ (~ ((x1 (x1 x2)) = (x1 x2)))).
Definition term315 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (x0 (x1 x2)) /\ ((x1 (x1 x2)) = x2).
Definition term380 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ~ ((~ ((x0 x1) = x1)) /\ ((x0 (x0 x1)) = x1)).
Definition term452 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := (((x0 (x0 x1)) = (x0 x1)) /\ ((x0 (x0 x1)) = x1)) -> (x0 x1) = x1.
Definition term413 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => (@IN a0 y0 x0) /\ ((x1 y0) = y0).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) /\ (x1 y0).
Definition term358 (a0 : Type') (x0 : a0 -> a0) := forall y0 : a0 -> Prop, ((forall y1 : a0, (y0 y1) -> (y0 (x0 y1)) /\ ((x0 (x0 y1)) = y1)) /\ (@FINITE a0 y0)) -> forall y1 : a0, ((y0 y1) /\ (~ ((x0 y1) = y1))) -> ((y0 (x0 y1)) /\ (~ ((x0 (x0 y1)) = (x0 y1)))) /\ ((~ ((x0 y1) = y1)) /\ ((x0 (x0 y1)) = y1)).
Definition term393 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := and (forall y0 : a0, (~ (@I (a0 -> Prop) x0 y0)) \/ ((@I (a0 -> Prop) x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0))).
Definition term368 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := and (forall y0 : a0, (~ (x0 y0)) \/ ((x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0))).
Definition term322 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := and (forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term321 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := and (forall y0 : a0, (@IN a0 y0 x0) -> (@IN a0 (x1 y0) x0) /\ ((x1 (x1 y0)) = y0)).
Definition term146 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ ((x2 y0) = y0)) y0.
Definition term64 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ (x2 x3))).
Definition term317 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (x0 x2) -> (x0 (x1 x2)) /\ ((x1 (x1 x2)) = x2).
Definition term209 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ ((x0 x2) /\ ((x1 x2) = x2))) /\ (~ ((x0 x2) /\ (~ ((x1 x2) = x2)))).
Definition term229 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1)).
Definition term408 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (@I (a0 -> Prop) x0 x2)) \/ ((x1 (x1 x2)) = x2).
Definition term409 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (@I (a0 -> Prop) x0 x1)) -> @I (a0 -> Prop) x0 x1.
Definition term216 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := or ((((x1 x2) /\ ((x0 x2) = x2)) \/ ((x1 x2) /\ (~ ((x0 x2) = x2)))) /\ (~ (x1 x2))).
Definition term336 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (x0 (x1 x2)) /\ (~ ((x1 (x1 x2)) = (x1 x2))).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term265 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ ((fun y0 : a0 => ~ ((x2 y0) = y0)) x3)).
Definition term420 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@I (a0 -> Prop) x0 (x1 x2)) -> False.
Definition term381 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := or (~ ((x0 (x1 x2)) /\ (~ ((x1 (x1 x2)) = (x1 x2))))).
Definition term102 (x0 : Prop) := (~ x0) -> x0.
Definition term120 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (x0 = y0) /\ (y0 = x1).
Definition term318 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => (@IN a0 y0 x0) -> (@IN a0 (x1 y0) x0) /\ ((x1 (x1 y0)) = y0).
Definition term206 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ~ ((x0 x2) /\ (~ ((x1 x2) = x2))).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) /\ (~ ((x1 y0) = y0))) x2.
Definition term18 (x0 : Prop) := (fun y0 : Prop => (y0 = (y0 = x0)) = x0) True.
Definition term298 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)))).
Definition term441 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0 -> a0, (@FINITE a0 y0) /\ (forall y2 : a0, (@IN a0 y2 y0) -> (@IN a0 (y1 y2) y0) /\ ((~ ((y1 y2) = y2)) /\ ((y1 (y1 y2)) = y2)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y0).
Definition term327 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := imp ((x0 x2) /\ (~ ((x1 x2) = x2))).
Definition term232 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ ((@INTER a0 x0 y0) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 y0)) = (Nat.add (@CARD a0 x0) (@CARD a0 y0)).
Definition term227 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 x0) -> @FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (y0 y2)) y2)).
Definition term436 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term350 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := ~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0))).
Definition term160 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => (@IN a0 y0 x0) /\ (~ ((x1 y0) = y0)).
Definition term417 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (@I (a0 -> Prop) x0 x1).
Definition term125 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (exists y2 : Prop, (y0 = y2) /\ (y2 = y1)) -> y0 = y1) x0.
Definition term275 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (@FINITE a0 x0) -> (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) = True.
Definition term261 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (@FINITE a0 x0) -> (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => ~ ((x1 y2) = y2)) y1)) y1))) = True.
Definition term259 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (@FINITE a0 x0) -> (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1))) = True.
Definition term244 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (@FINITE a0 x0) -> (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => (x1 y2) = y2) y1)) y1))) = True.
Definition term243 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1))) = True.
Definition term432 (a0 : Type') (x0 : a0) (x1 : a0) := or (~ (x0 = x1)).
Definition term397 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ~ (x0 (x1 x2)).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) /\ (x1 x2)) /\ ((x0 x2) /\ (~ (x1 x2))).
Definition term221 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ((x0 x1) = x1) -> False.
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x1 x2).
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y1) y1.
Definition term149 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ ((x1 y2) = y2)) y1) y1.
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ (~ (x1 y2))) y1) y1.
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ (x1 y2)) y1) y1.
Definition term343 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ((x0 x2) /\ (~ ((x1 x2) = x2))) -> ((x0 (x1 x2)) /\ (~ ((x1 (x1 x2)) = (x1 x2)))) /\ ((~ ((x1 x2) = x2)) /\ ((x1 (x1 x2)) = x2)).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ((x0 x2) /\ ((x1 x2) = x2)) \/ ((x0 x2) /\ (~ ((x1 x2) = x2))).
Definition term214 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (((x1 x2) /\ ((x0 x2) = x2)) \/ ((x1 x2) /\ (~ ((x0 x2) = x2))))) /\ (x1 x2).
Definition term182 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := fun y0 : a0 => (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0).
Definition term434 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term234 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ ((@INTER a0 x0 x1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 x1)) = (Nat.add (@CARD a0 x0) (@CARD a0 x1)).
Definition term325 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := imp ((forall y0 : a0, (x1 y0) -> (x1 (x0 y0)) /\ ((x0 (x0 y0)) = y0)) /\ (@FINITE a0 x1)).
Definition term324 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := imp ((forall y0 : a0, (@IN a0 y0 x1) -> (@IN a0 (x0 y0) x1) /\ ((x0 (x0 y0)) = y0)) /\ (@FINITE a0 x1)).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ~ (((y0 y1) /\ (x0 y1)) /\ ((y0 y1) /\ (~ (x0 y1)))).
Definition term131 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term299 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (fun y0 : Prop => y0 = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))))) ((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)))) = ((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1)))))).
Definition term240 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0))) x1.
Definition term391 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => (~ (@I (a0 -> Prop) x0 y0)) \/ ((@I (a0 -> Prop) x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term411 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := @eq Prop ((~ (@I (a0 -> Prop) x0 x2)) \/ (@I (a0 -> Prop) x0 (x1 x2))).
Definition term377 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := or ((x0 x1) = x1).
Definition term394 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := (forall y0 : a0, (~ (@I (a0 -> Prop) x1 y0)) \/ ((@I (a0 -> Prop) x1 (x0 y0)) /\ ((x0 (x0 y0)) = y0))) /\ (@FINITE a0 x1).
Definition term369 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := (forall y0 : a0, (~ (x1 y0)) \/ ((x1 (x0 y0)) /\ ((x0 (x0 y0)) = y0))) /\ (@FINITE a0 x1).
Definition term323 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := (forall y0 : a0, (x1 y0) -> (x1 (x0 y0)) /\ ((x0 (x0 y0)) = y0)) /\ (@FINITE a0 x1).
Definition term306 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := (forall y0 : a0, (@IN a0 y0 x1) -> (@IN a0 (x0 y0) x1) /\ ((x0 (x0 y0)) = y0)) /\ (@FINITE a0 x1).
Definition term447 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (x1 = x0) /\ (x1 = x2).
Definition term387 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@I (a0 -> Prop) x0 (x1 x2)) /\ ((x1 (x1 x2)) = x2).
Definition term142 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ ((x2 x3) = x3)).
Definition term290 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @eq (a0 -> Prop) (@INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))).
Definition term289 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @eq (a0 -> Prop) (@INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => (x1 y2) = y2) y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((fun y2 : a0 => (x1 y2) = y2) y1))) y1))).
Definition term173 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y1)).
Definition term158 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (~ ((x2 y2) = y2))) y1) y1)).
Definition term152 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x2 y1) = y1)) y1)).
Definition term137 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ ((x2 y2) = y2)) y1) y1)).
Definition term74 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ (x2 y1))) y1)).
Definition term59 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (~ (x2 y2))) y1) y1)).
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1)).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (x2 y2)) y1) y1)).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (@IN a0 x2 x0) /\ (~ (x1 x2)).
Definition term23 (x0 : Prop) := ~ (False = x0).
Definition term326 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := imp (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y1))).
Definition term366 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => (~ (x0 y0)) \/ ((x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) /\ (x1 y0)) x2.
Definition term406 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (fun y0 : a0 => ((~ (@I (a0 -> Prop) x0 y0)) \/ (@I (a0 -> Prop) x0 (x1 y0))) /\ ((~ (@I (a0 -> Prop) x0 y0)) \/ ((x1 (x1 y0)) = y0))) x2.
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (x0 x2) /\ (~ ((x1 x2) = x2)).
Definition term346 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term303 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) -> (@IN a0 (x1 y0) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term304 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) /\ (forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) -> (@IN a0 (x1 y0) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0))).
Definition term246 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := (fun y0 : a0 => (x0 y0) = y0) x1.
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term213 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := and (((~ (x0 x2)) \/ (~ ((x1 x2) = x2))) /\ ((~ (x0 x2)) \/ ((x1 x2) = x2))).
Definition term175 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y1))).
Definition term174 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (~ ((x2 y2) = y2))) y1) y1))).
Definition term154 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x2 y1) = y1)) y1))).
Definition term153 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ ((x2 y2) = y2)) y1) y1))).
Definition term76 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ (x2 y1))) y1))).
Definition term75 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (~ (x2 y2))) y1) y1))).
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1))).
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (x2 y2)) y1) y1))).
Definition term364 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ~ (((x0 (x1 x2)) /\ (~ ((x1 (x1 x2)) = (x1 x2)))) /\ ((~ ((x1 x2) = x2)) /\ ((x1 (x1 x2)) = x2))).
Definition term401 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := or ((~ (@I (a0 -> Prop) x0 (x1 x2))) \/ ((x1 (x1 x2)) = (x1 x2))).
Definition term405 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := forall y0 : a0, ((~ (@I (a0 -> Prop) x0 y0)) \/ (@I (a0 -> Prop) x0 (x1 y0))) /\ ((~ (@I (a0 -> Prop) x0 y0)) \/ ((x1 (x1 y0)) = y0)).
Definition term334 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@IN a0 (x1 x2) x0) /\ (~ ((x1 (x1 x2)) = (x1 x2))).
Definition term133 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @IN a0 x0 (@UNION a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x2 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y1))).
Definition term389 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (@I (a0 -> Prop) x0 x1)).
Definition term396 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@I (a0 -> Prop) x0 x2) /\ (~ ((x1 x2) = x2)).
Definition term283 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((fun y0 : a0 => (x2 y0) = y0) x3))) x3.
Definition term427 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@I (a0 -> Prop) x0 x2) -> (x1 (x1 x2)) = x2.
Definition term460 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := fun y0 : Prop => ((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ ((x0 y2) = y2)) y2)))) = y0) /\ (y0 = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 x1))).
Definition term111 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, ((y0 = y1) /\ (y1 = y2)) -> y0 = y2) x0.
Definition term351 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := ((~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))) -> False) -> (~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))) -> False.
Definition term186 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))) -> False) -> (~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))) -> False.
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term144 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ ((x2 x3) = x3)) x3.
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((x0 x2) /\ (x1 x2)).
Definition term212 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := and (~ (((x0 x2) /\ ((x1 x2) = x2)) \/ ((x0 x2) /\ (~ ((x1 x2) = x2))))).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x0 x2) /\ (x1 x2)) /\ ((x0 x2) /\ (~ (x1 x2)))) -> False.
Definition term198 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := (~ ((((x1 x2) /\ ((x0 x2) = x2)) \/ ((x1 x2) /\ (~ ((x0 x2) = x2)))) = (x1 x2))) -> False.
Definition term415 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (@I (a0 -> Prop) x0 x1)).
Definition term288 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1)).
Definition term277 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => (x1 y2) = y2) y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((fun y2 : a0 => (x1 y2) = y2) y1))) y1)).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (x1 y1))) y1)).
Definition term287 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((fun y2 : a0 => (x1 y2) = y2) y1))) y1).
Definition term270 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => ~ ((x1 y2) = y2)) y1)) y1).
Definition term253 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => (x1 y2) = y2) y1)) y1).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y1) y1).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ ((x1 y2) = y2)) y1) y1).
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ (~ (x1 y2))) y1) y1).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ (x1 y2)) y1) y1).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (x1 y1))) y1).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))).
Definition term454 (a0 : Type') (x0 : a0 -> a0) := (fun y0 : a0 -> a0 => forall y1 : a0 -> Prop, (~ (((forall y2 : a0, (y1 y2) -> (y1 (y0 y2)) /\ ((y0 (y0 y2)) = y2)) /\ (@FINITE a0 y1)) -> forall y2 : a0, ((y1 y2) /\ (~ ((y0 y2) = y2))) -> ((y1 (y0 y2)) /\ (~ ((y0 (y0 y2)) = (y0 y2)))) /\ ((~ ((y0 y2) = y2)) /\ ((y0 (y0 y2)) = y2)))) -> False) x0.
Definition term453 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ((x0 (x0 x1)) = x1) -> False.
Definition term66 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ (x2 x3))) x3.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0 -> a0, (@FINITE a0 x0) /\ (forall y1 : a0, (@IN a0 y1 x0) -> (@IN a0 (y0 y1) x0) /\ ((~ ((y0 y1) = y1)) /\ ((y0 (y0 y1)) = y1)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 x0).
Definition term440 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term183 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0).
Definition term361 (a0 : Type') := forall y0 : a0 -> a0, forall y1 : a0 -> Prop, (~ (((forall y2 : a0, (y1 y2) -> (y1 (y0 y2)) /\ ((y0 (y0 y2)) = y2)) /\ (@FINITE a0 y1)) -> forall y2 : a0, ((y1 y2) /\ (~ ((y0 y2) = y2))) -> ((y1 (y0 y2)) /\ (~ ((y0 (y0 y2)) = (y0 y2)))) /\ ((~ ((y0 y2) = y2)) /\ ((y0 (y0 y2)) = y2)))) -> False.
Definition term196 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a0, (~ (forall y2 : a0, (((y0 y2) /\ ((y1 y2) = y2)) \/ ((y0 y2) /\ (~ ((y1 y2) = y2)))) = (y0 y2))) -> False.
Definition term99 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y1 y2) /\ (y0 y2)) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term248 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ ((fun y0 : a0 => (x2 y0) = y0) x3)).
Definition term22 (x0 : Prop) := @eq Prop (True = (True = x0)).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))).
Definition term208 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := and ((~ (x0 x2)) \/ (~ ((x1 x2) = x2))).
Definition term80 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ (x2 y1))) y1)))).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term166 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y0) y0.
Definition term145 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ ((x2 y1) = y1)) y0) y0.
Definition term67 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ (~ (x2 y1))) y0) y0.
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ (x2 y1)) y0) y0.
Definition term126 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (exists y1 : Prop, (x0 = y1) /\ (y1 = y0)) -> x0 = y0) x1.
Definition term239 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term285 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((fun y1 : a0 => (x2 y1) = y1) y0))) y0.
Definition term268 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ ((fun y1 : a0 => ~ ((x2 y1) = y1)) y0)) y0.
Definition term251 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ ((fun y1 : a0 => (x2 y1) = y1) y0)) y0.
Definition term169 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((x2 y0) = y0))) y0.
Definition term148 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ ((x2 y0) = y0)) y0.
Definition term70 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ (x2 y0))) y0.
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (x2 y0)) y0.
Definition term300 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @eq Prop ((fun y0 : Prop => y0 = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))))) ((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)))) = ((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))))))).
Definition term392 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := forall y0 : a0, (~ (@I (a0 -> Prop) x0 y0)) \/ ((@I (a0 -> Prop) x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term367 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := forall y0 : a0, (~ (x0 y0)) \/ ((x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)).
Definition term117 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 = x1) /\ (x1 = x2).
Definition term247 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@IN a0 x2 x0) /\ ((fun y0 : a0 => (x1 y0) = y0) x2).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := @eq Prop (((x0 x2) /\ ((x1 x2) = x2)) \/ ((x0 x2) /\ (~ ((x1 x2) = x2)))).
Definition term419 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (@I (a0 -> Prop) x0 (x1 x2))) -> @I (a0 -> Prop) x0 (x1 x2).
Definition term295 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1))).
Definition term262 (a0 : Type') (x0 : a0 -> a0) := fun y0 : a0 => ~ ((x0 y0) = y0).
Definition term359 (a0 : Type') := fun y0 : a0 -> a0 => forall y1 : a0 -> Prop, (~ (((forall y2 : a0, (y1 y2) -> (y1 (y0 y2)) /\ ((y0 (y0 y2)) = y2)) /\ (@FINITE a0 y1)) -> forall y2 : a0, ((y1 y2) /\ (~ ((y0 y2) = y2))) -> ((y1 (y0 y2)) /\ (~ ((y0 (y0 y2)) = (y0 y2)))) /\ ((~ ((y0 y2) = y2)) /\ ((y0 (y0 y2)) = y2)))) -> False.
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0))))).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (((x0 x2) /\ (x1 x2)) /\ ((x0 x2) /\ (~ (x1 x2)))).
Definition term231 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1))) x0.
Definition term226 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (y1 y3)) y3))) x0.
Definition term294 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := Coq.Arith.PeanoNat.Nat.Even (Nat.add (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1))) (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1)))).
Definition term134 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x2 y1) = y1)) y1))) \/ (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y1))).
Definition term233 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ ((@INTER a0 x0 y0) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 y0)) = (Nat.add (@CARD a0 x0) (@CARD a0 y0))) x1.
Definition term189 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))).
Definition term241 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 x1).
Definition term433 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term207 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := and (~ ((x0 x2) /\ ((x1 x2) = x2))).
Definition term191 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a0 => forall y1 : a0, (((x0 y1) /\ ((y0 y1) = y1)) \/ ((x0 y1) /\ (~ ((y0 y1) = y1)))) = (x0 y1).
Definition term184 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := (~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))) -> False.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term121 (x0 : Prop) (x1 : Prop) := (exists y0 : Prop, (x0 = y0) /\ (y0 = x1)) -> x0 = x1.
Definition term309 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 (x0 x1) x2.
Definition term312 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := and (x0 (x1 x2)).
Definition term457 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 -> a0 => (@FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) /\ (forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((x1 y3) = y3))) y3))) -> (@IN a0 (y0 y1) (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((x1 y3) = y3))) y3))) /\ ((~ ((y0 y1) = y1)) /\ ((y0 (y0 y1)) = y1))).
Definition term455 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (((forall y1 : a0, (y0 y1) -> (y0 (x0 y1)) /\ ((x0 (x0 y1)) = y1)) /\ (@FINITE a0 y0)) -> forall y1 : a0, ((y0 y1) /\ (~ ((x0 y1) = y1))) -> ((y0 (x0 y1)) /\ (~ ((x0 (x0 y1)) = (x0 y1)))) /\ ((~ ((x0 y1) = y1)) /\ ((x0 (x0 y1)) = y1)))) -> False) x1.
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ (((y0 y1) /\ (x0 y1)) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False) x1.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0 -> a0, (@FINITE a0 y0) /\ (forall y2 : a0, (@IN a0 y2 y0) -> (@IN a0 (y1 y2) y0) /\ ((~ ((y1 y2) = y2)) /\ ((y1 (y1 y2)) = y2)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y0)) x0.
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x0 x2) /\ (x1 x2)) /\ ((x0 x2) /\ (~ (x1 x2)))).
Definition term437 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term446 (a0 : Type') (x0 : a0) (x1 : a0) := and (x0 = x1).
Definition term225 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@UNION a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1)))).
Definition term292 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1))) /\ ((@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) /\ ((@INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) = (@EMPTY a0))).
Definition term293 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := Nat.add (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1))) (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0 -> a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> (@IN a0 (y0 y2) y1) /\ ((~ ((y0 y2) = y2)) /\ ((y0 (y0 y2)) = y2)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y1)) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 x0).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1))) /\ (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ (x2 y1))) y1))).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (@IN a0 x2 x0) /\ (x1 x2).
Definition term352 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (((~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))) -> False) -> (~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))) -> False) -> (~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))) -> False.
Definition term187 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))) -> False) -> (~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))) -> False) -> (~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))) -> False.
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term15 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term357 (a0 : Type') (x0 : a0 -> a0) := forall y0 : a0 -> Prop, (~ (((forall y1 : a0, (y0 y1) -> (y0 (x0 y1)) /\ ((x0 (x0 y1)) = y1)) /\ (@FINITE a0 y0)) -> forall y1 : a0, ((y0 y1) /\ (~ ((x0 y1) = y1))) -> ((y0 (x0 y1)) /\ (~ ((x0 (x0 y1)) = (x0 y1)))) /\ ((~ ((x0 y1) = y1)) /\ ((x0 (x0 y1)) = y1)))) -> False.
Definition term192 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a0, (~ (forall y1 : a0, (((x0 y1) /\ ((y0 y1) = y1)) \/ ((x0 y1) /\ (~ ((y0 y1) = y1)))) = (x0 y1))) -> False.
Definition term95 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, ~ (((y0 y1) /\ (x0 y1)) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term360 (a0 : Type') := fun y0 : a0 -> a0 => forall y1 : a0 -> Prop, ((forall y2 : a0, (y1 y2) -> (y1 (y0 y2)) /\ ((y0 (y0 y2)) = y2)) /\ (@FINITE a0 y1)) -> forall y2 : a0, ((y1 y2) /\ (~ ((y0 y2) = y2))) -> ((y1 (y0 y2)) /\ (~ ((y0 (y0 y2)) = (y0 y2)))) /\ ((~ ((y0 y2) = y2)) /\ ((y0 (y0 y2)) = y2)).
Definition term373 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (x0 (x1 x2))) \/ ((x1 (x1 x2)) = (x1 x2)).
Definition term286 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((fun y2 : a0 => (x1 y2) = y2) y1))) y1.
Definition term269 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => ~ ((x1 y2) = y2)) y1)) y1.
Definition term252 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => (x1 y2) = y2) y1)) y1.
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1.
Definition term150 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (x1 y1))) y1.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1.
Definition term123 := forall y0 : Prop, forall y1 : Prop, (exists y2 : Prop, (y0 = y2) /\ (y2 = y1)) -> y0 = y1.
Definition term112 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, ((x0 = y0) /\ (y0 = y1)) -> x0 = y1.
Definition term110 := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, ((y0 = y1) /\ (y1 = y2)) -> y0 = y2.
Definition term127 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := (exists y0 : Prop, ((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ ((x0 y2) = y2)) y2)))) = y0) /\ (y0 = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 x1)))) -> (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x0 y1) = y1)) y1)))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 x1)).
Definition term307 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term224 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @CARD a0 (@UNION a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))).
Definition term445 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (~ (x0 = x1))).
Definition term388 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (@I (a0 -> Prop) x0 x1).
Definition term431 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term430 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term3 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> (@IN a0 (x0 y1) y0) /\ ((~ ((x0 y1) = y1)) /\ ((x0 (x0 y1)) = y1)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y0)) x1.
Definition term463 (a0 : Type') := forall y0 : a0 -> a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> (@IN a0 (y0 y2) y1) /\ ((y0 (y0 y2)) = y2))) -> (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ ((y0 y3) = y3)) y3)))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y1)).
Definition term362 (a0 : Type') := forall y0 : a0 -> a0, forall y1 : a0 -> Prop, ((forall y2 : a0, (y1 y2) -> (y1 (y0 y2)) /\ ((y0 (y0 y2)) = y2)) /\ (@FINITE a0 y1)) -> forall y2 : a0, ((y1 y2) /\ (~ ((y0 y2) = y2))) -> ((y1 (y0 y2)) /\ (~ ((y0 (y0 y2)) = (y0 y2)))) /\ ((~ ((y0 y2) = y2)) /\ ((y0 (y0 y2)) = y2)).
Definition term0 (a0 : Type') := forall y0 : a0 -> a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> (@IN a0 (y0 y2) y1) /\ ((~ ((y0 y2) = y2)) /\ ((y0 (y0 y2)) = y2)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y1).
Definition term124 := (forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, ((y0 = y1) /\ (y1 = y2)) -> y0 = y2) -> forall y0 : Prop, forall y1 : Prop, (exists y2 : Prop, (y0 = y2) /\ (y2 = y1)) -> y0 = y1.
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ (x2 y1))) y1))).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a0 => (@FINITE a0 x0) /\ (forall y1 : a0, (@IN a0 y1 x0) -> (@IN a0 (y0 y1) x0) /\ ((~ ((y0 y1) = y1)) /\ ((y0 (y0 y1)) = y1))).
Definition term399 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := or (~ (@I (a0 -> Prop) x0 (x1 x2))).
Definition term282 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((fun y0 : a0 => (x2 y0) = y0) x3))).
Definition term365 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (x0 x2)) \/ ((x0 (x1 x2)) /\ ((x1 (x1 x2)) = x2)).
Definition term337 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := and (@IN a0 (x2 x0) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y1))).
Definition term412 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((@I (a0 -> Prop) x1 (x0 x2)) \/ (~ (@I (a0 -> Prop) x1 x2))).
Definition term25 (x0 : Prop) := @eq Prop (False = (False = x0)).
Definition term395 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (@I (a0 -> Prop) x0 x1).
Definition term179 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @eq Prop (@IN a0 x0 (@UNION a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x2 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y1)))).
Definition term308 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term165 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((x2 x3) = x3))) x3.
Definition term194 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a0, (~ (forall y2 : a0, (((y0 y2) /\ ((y1 y2) = y2)) \/ ((y0 y2) /\ (~ ((y1 y2) = y2)))) = (y0 y2))) -> False.
Definition term97 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ (((y1 y2) /\ (y0 y2)) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) /\ (~ (x1 y0)).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (@IN a0 x1 x2).
Definition term458 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := ((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x0 y1) = y1)) y1)))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@UNION a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x0 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x0 y1) = y1))) y1)))))) /\ ((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@UNION a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x0 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x0 y1) = y1))) y1))))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 x1))).
Definition term2 (a0 : Type') (x0 : a0 -> a0) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> (@IN a0 (x0 y1) y0) /\ ((~ ((x0 y1) = y1)) /\ ((x0 (x0 y1)) = y1)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y0).
Definition term238 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) x0.
Definition term331 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @IN a0 (x2 x0) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = y1))) y1)).
Definition term328 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := @IN a0 (x2 x0) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (~ ((x2 y2) = y2))) y1) y1)).
Definition term390 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (@I (a0 -> Prop) x0 x2)) \/ ((@I (a0 -> Prop) x0 (x1 x2)) /\ ((x1 (x1 x2)) = x2)).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := or ((x0 x2) /\ ((x1 x2) = x2)).
Definition term311 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) (x2 : a0 -> Prop) := and (@IN a0 (x0 x1) x2).
Definition term274 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @eq Prop (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))).
Definition term273 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @eq Prop (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => ~ ((x1 y2) = y2)) y1)) y1))).
Definition term257 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @eq Prop (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1))).
Definition term256 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @eq Prop (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => (x1 y2) = y2) y1)) y1))).
Definition term459 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := exists y0 : Prop, ((Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ ((x0 y2) = y2)) y2)))) = y0) /\ (y0 = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 x1))).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INTER a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (x1 y2)) y2)) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (x1 y2))) y2)))) = (@IN a0 y0 (@EMPTY a0)).
Definition term320 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0).
Definition term57 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := and (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1))).
Definition term378 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := (~ (~ ((x0 x1) = x1))) \/ (~ ((x0 (x0 x1)) = x1)).
Definition term398 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ~ (@I (a0 -> Prop) x0 (x1 x2)).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (x2 y0)) y0.
Definition term302 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (exists y0 : a0 -> a0, (@FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = y2))) y2))) /\ (forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((x1 y3) = y3))) y3))) -> (@IN a0 (y0 y1) (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((x1 y3) = y3))) y3))) /\ ((~ ((y0 y1) = y1)) /\ ((y0 (y0 y1)) = y1)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))).
Definition term280 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ~ ((fun y0 : a0 => (x0 y0) = y0) x1).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) /\ (~ (x1 y0))) x2.
Definition term114 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, ((x1 = x0) /\ (x0 = y0)) -> x1 = y0.
Definition term442 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> (@IN a0 (x1 y0) x0) /\ ((x1 (x1 y0)) = y0)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> (@IN a0 (x1 y0) x0) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0))).
Definition term279 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)).
Definition term278 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => (x1 y2) = y2) y1)) y1)).
Definition term204 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (x0 x2)) \/ (~ (~ ((x1 x2) = x2))).
Definition term439 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term201 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (x0 x2)) \/ (~ ((x1 x2) = x2)).
Definition term122 (x0 : Prop) := forall y0 : Prop, (exists y1 : Prop, (x0 = y1) /\ (y1 = y0)) -> x0 = y0.
Definition term119 (x0 : Prop) (x1 : Prop) := exists y0 : Prop, (x0 = y0) /\ (y0 = x1).
Definition term339 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := (~ ((x0 x1) = x1)) /\ ((x0 (x0 x1)) = x1).
Definition term435 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term404 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := fun y0 : a0 => ((~ (@I (a0 -> Prop) x0 y0)) \/ (@I (a0 -> Prop) x0 (x1 y0))) /\ ((~ (@I (a0 -> Prop) x0 y0)) \/ ((x1 (x1 y0)) = y0)).
Definition term400 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (@I (a0 -> Prop) x0 (x1 x2))) \/ ((x1 (x1 x2)) = (x1 x2)).
Definition term267 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ ((fun y1 : a0 => ~ ((x2 y1) = y1)) y0)) y0.
Definition term250 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ ((fun y1 : a0 => (x2 y1) = y1) y0)) y0.
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term340 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@IN a0 (x1 x2) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) /\ ((~ ((x1 x2) = x2)) /\ ((x1 (x1 x2)) = x2)).
Definition term223 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (fun y0 : a0 -> a0 => (~ (forall y1 : a0, (((x0 y1) /\ ((y0 y1) = y1)) \/ ((x0 y1) /\ (~ ((y0 y1) = y1)))) = (x0 y1))) -> False) x1.
Definition term113 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 = y0) /\ (y0 = y1)) -> x0 = y1) x1.
Definition term330 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := @IN a0 (x0 x1).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := forall y0 : a0, (@IN a0 y0 x0) -> (@IN a0 (x1 y0) x0) /\ ((x1 (x1 y0)) = y0).
Definition term200 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ~ ((x0 x2) /\ ((x1 x2) = x2)).
Definition term202 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ~ (~ ((x0 x1) = x1)).
Definition term438 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term217 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := ((((x1 x2) /\ ((x0 x2) = x2)) \/ ((x1 x2) /\ (~ ((x0 x2) = x2)))) /\ (~ (x1 x2))) \/ ((~ (((x1 x2) /\ ((x0 x2) = x2)) \/ ((x1 x2) /\ (~ ((x0 x2) = x2))))) /\ (x1 x2)).
Definition term421 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term236 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @CARD a0 (@UNION a0 x0 x1).
Definition term245 (a0 : Type') (x0 : a0 -> a0) := fun y0 : a0 => (x0 y0) = y0.
Definition term116 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x1 = x0) /\ (x0 = x2)) -> x1 = x2.
Definition term426 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (~ (@I (a0 -> Prop) x0 x2))) -> (x1 (x1 x2)) = x2.
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (x0 x2) /\ ((x1 x2) = x2).
Definition term335 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ~ ((x0 (x0 x1)) = (x0 x1)).
Definition term156 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) := or (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x2 y1) = y1)) y1))).
Definition term195 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a0, forall y2 : a0, (((y0 y2) /\ ((y1 y2) = y2)) \/ ((y0 y2) /\ (~ ((y1 y2) = y2)))) = (y0 y2).
Definition term98 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ~ (((y1 y2) /\ (y0 y2)) /\ ((y1 y2) /\ (~ (y0 y2)))).
Definition term20 (x0 : Prop) (x1 : Prop) := @eq Prop ((x0 = (x0 = x1)) = x1).
Definition term353 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (((~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))) -> False) -> (~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))) -> False) -> ((~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))) -> False) -> (~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))) -> False.
Definition term188 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))) -> False) -> (~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))) -> False) -> ((~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))) -> False) -> (~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0))) -> False.
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> ((~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ (((x0 y0) /\ (x1 y0)) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term130 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@UNION a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ ((x0 y2) = y2)) y2)) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (~ ((x0 y2) = y2))) y2)))) = (@IN a0 y0 x1).
Definition term164 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ (~ ((x2 y0) = y0))) x3) x3.
Definition term143 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ ((x2 y0) = y0)) x3) x3.
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ (~ (x2 y0))) x3) x3.
Definition term42 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ (x2 y0)) x3) x3.
Definition term297 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1)).
Definition term296 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := @CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)).
Definition term370 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ~ (~ ((x0 (x0 x1)) = (x0 x1))).
Definition term355 (a0 : Type') (x0 : a0 -> a0) := fun y0 : a0 -> Prop => (~ (((forall y1 : a0, (y0 y1) -> (y0 (x0 y1)) /\ ((x0 (x0 y1)) = y1)) /\ (@FINITE a0 y0)) -> forall y1 : a0, ((y0 y1) /\ (~ ((x0 y1) = y1))) -> ((y0 (x0 y1)) /\ (~ ((x0 (x0 y1)) = (x0 y1)))) /\ ((~ ((x0 y1) = y1)) /\ ((x0 (x0 y1)) = y1)))) -> False.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ (((y0 y1) /\ (x0 y1)) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term349 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := (~ (((forall y0 : a0, (x0 y0) -> (x0 (x1 y0)) /\ ((x1 (x1 y0)) = y0)) /\ (@FINITE a0 x0)) -> forall y0 : a0, ((x0 y0) /\ (~ ((x1 y0) = y0))) -> ((x0 (x1 y0)) /\ (~ ((x1 (x1 y0)) = (x1 y0)))) /\ ((~ ((x1 y0) = y0)) /\ ((x1 (x1 y0)) = y0)))) -> False.
Definition term161 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@IN a0 x2 x0) /\ (~ ((x1 x2) = x2)).
Definition term375 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ~ ((x0 (x0 x1)) = x1).
Definition term418 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@I (a0 -> Prop) x0 x2) -> @I (a0 -> Prop) x0 (x1 x2).
Definition term237 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Nat.add (@CARD a0 x0) (@CARD a0 x1).
Definition term449 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term1 (a0 : Type') (x0 : a0 -> a0) := (fun y0 : a0 -> a0 => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> (@IN a0 (y0 y2) y1) /\ ((~ ((y0 y2) = y2)) /\ ((y0 (y0 y2)) = y2)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD a0 y1)) x0.
Definition term176 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := ~ ((x0 x1) = x1).
Definition term242 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := ((@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1))) /\ ((@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) /\ ((@INTER a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1)))) = (Nat.add (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1))) (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1)))).
Definition term14 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term338 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := and ((x0 (x1 x2)) /\ (~ ((x1 (x1 x2)) = (x1 x2)))).
Definition term276 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := and (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))).
Definition term260 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) := and (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((x1 y1) = y1)) y1))).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) /\ ((x1 y0) = y0)) x2.
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@IN a0 x2 x0) /\ ((x1 x2) = x2).
Definition term19 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = (y0 = x0)) = x0) x1).
Definition term163 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((x2 x3) = x3))).
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term210 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ((~ (x0 x2)) \/ (~ ((x1 x2) = x2))) /\ ((~ (x0 x2)) \/ ((x1 x2) = x2)).
Definition term185 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := ~ (forall y0 : a0, (((x1 y0) /\ ((x0 y0) = y0)) \/ ((x1 y0) /\ (~ ((x0 y0) = y0)))) = (x1 y0)).
Definition term314 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@IN a0 (x1 x2) x0) /\ ((x1 (x1 x2)) = x2).
Definition term193 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a0, forall y1 : a0, (((x0 y1) /\ ((y0 y1) = y1)) \/ ((x0 y1) /\ (~ ((y0 y1) = y1)))) = (x0 y1).
Definition term371 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := or (~ (x0 (x1 x2))).
Definition term219 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) /\ ((x0 x2) = x2)) \/ ((x1 x2) /\ (~ ((x0 x2) = x2)))) /\ (~ (x1 x2)).
Definition term342 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (@IN a0 x2 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) -> (@IN a0 (x1 x2) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = y1))) y1))) /\ ((~ ((x1 x2) = x2)) /\ ((x1 (x1 x2)) = x2)).
Definition term444 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term341 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ((x0 (x1 x2)) /\ (~ ((x1 (x1 x2)) = (x1 x2)))) /\ ((~ ((x1 x2) = x2)) /\ ((x1 (x1 x2)) = x2)).
Definition term266 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ ((fun y0 : a0 => ~ ((x2 y0) = y0)) x3)) x3.
Definition term249 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ ((fun y0 : a0 => (x2 y0) = y0) x3)) x3.
Definition term199 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((((x1 x2) /\ ((x0 x2) = x2)) \/ ((x1 x2) /\ (~ ((x0 x2) = x2)))) = (x1 x2)).
Definition term423 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := ((x0 (x0 x2)) = x2) \/ (~ (@I (a0 -> Prop) x1 x2)).
Definition term461 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> (@IN a0 (x0 y0) x1) /\ ((x0 (x0 y0)) = y0))) -> (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((x0 y1) = y1)) y1)))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD a0 x1)).
Definition term21 (x0 : Prop) := (fun y0 : Prop => (y0 = (y0 = x0)) = x0) False.
Definition term416 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (~ (~ (@I (a0 -> Prop) x0 x1))).
Definition term376 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := or (~ (~ ((x0 x1) = x1))).
Definition term40 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ (x2 y0)) x3).
Definition term211 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ~ (((x0 x2) /\ ((x1 x2) = x2)) \/ ((x0 x2) /\ (~ ((x1 x2) = x2)))).
