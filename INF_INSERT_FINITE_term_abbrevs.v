Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term199 (x0 : real -> Prop) := forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0.
Definition term158 (x0 : real) (x1 : real -> Prop) := forall y0 : real, (@IN real y0 x1) -> real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)) y0.
Definition term140 (x0 : real) (x1 : real -> Prop) := forall y0 : real, (@IN real y0 x1) -> real_le (real_min x0 (inf x1)) y0.
Definition term41 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term50 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, ~ ((@INSERT a0 y0 y1) = (@EMPTY a0))) x0.
Definition term176 (x0 : real -> Prop) (x1 : real) := (real_le x1 (inf x0)) -> (@IN real x1 (@INSERT real x1 x0)) /\ ((real_le x1 x1) /\ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)).
Definition term31 (x0 : real -> Prop) (x1 : real) := (x0 = (@EMPTY real)) -> (fun y0 : real => (inf (@INSERT real x1 x0)) = y0) x1.
Definition term429 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term407 (x0 : real) (x1 : real -> Prop) := imp (~ ((~ (@FINITE real x1)) \/ ((x1 = (@EMPTY real)) \/ (~ (@IN real x0 x1))))).
Definition term72 (x0 : real) := and (@IN real x0 (@INSERT real x0 (@EMPTY real))).
Definition term335 (x0 : real -> Prop) := ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ (forall y0 : real, (@IN real (inf x0) x0) /\ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0))).
Definition term316 (x0 : real -> Prop) := ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((@IN real (inf x0) x0) /\ (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le (inf x0) y0))).
Definition term283 (x0 : real -> Prop) := ~ (all x0).
Definition term431 := (~ False) -> False.
Definition term205 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term336 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term200 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (@IN real y0 x0) -> real_le (inf x0) y0) x1.
Definition term246 := imp (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2).
Definition term243 := imp (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term255 (x0 : real -> Prop) (x1 : real) := (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term254 (x0 : real -> Prop) (x1 : real) := (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term170 (x0 : real) (x1 : real -> Prop) := (~ (real_le x0 (inf x1))) -> (fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) /\ ((real_le y0 x0) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1))) (inf x1).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@FINITE a0 (@INSERT a0 y1 y0)) = (@FINITE a0 y0)) x0.
Definition term108 (x0 : real) (x1 : real) := False -> (real_le x0 x1) = (real_le x0 x1).
Definition term165 (x0 : real) (x1 : real -> Prop) := ((real_le x0 (inf x1)) -> (fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) /\ ((real_le y0 x0) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1))) x0) /\ ((~ (real_le x0 (inf x1))) -> (fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) /\ ((real_le y0 x0) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1))) (inf x1)).
Definition term268 := fun y0 : real -> Prop => ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1).
Definition term150 (x0 : real) (x1 : real -> Prop) := and (@IN real (@COND real (real_le x0 (inf x1)) x0 (inf x1)) (@INSERT real x0 x1)).
Definition term293 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_le x0 x1) /\ (real_le x1 x2))).
Definition term381 (x0 : real -> Prop) := or (x0 = (@EMPTY real)).
Definition term185 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1))) x1.
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 (@INSERT a0 y0 y1)) -> x0 y2) = ((x0 y0) /\ (forall y2 : a0, (@IN a0 y2 y1) -> x0 y2))) x1.
Definition term231 (x0 : real -> Prop) (x1 : real) := (real_le (inf x0) x1) /\ True.
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 (@INSERT a0 x0 y0)) -> x1 y1) = ((x1 x0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> x1 y1))) x2.
Definition term171 (x0 : real) (x1 : real -> Prop) := (~ (real_le x0 (inf x1))) -> (@IN real (inf x1) (@INSERT real x0 x1)) /\ ((real_le (inf x1) x0) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (inf x1) y0)).
Definition term383 (x0 : real -> Prop) (x1 : real) := @eq Prop ((~ (@FINITE real x0)) \/ ((x0 = (@EMPTY real)) \/ ((~ (@IN real x1 x0)) \/ (real_le (inf x0) x1)))).
Definition term25 (x0 : real) (x1 : real -> Prop) := inf (@INSERT real x0 x1).
Definition term398 (x0 : Prop) := ~ (~ x0).
Definition term365 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2)).
Definition term306 (x0 : real -> Prop) := (~ (@FINITE real x0)) \/ (~ (~ (x0 = (@EMPTY real)))).
Definition term400 (x0 : real -> Prop) := and (~ (~ (@FINITE real x0))).
Definition term232 (x0 : real -> Prop) (x1 : real) := True /\ (real_le (inf x0) x1).
Definition term251 (x0 : real -> Prop) (x1 : real) := (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term289 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) /\ (~ (real_le x1 y0)).
Definition term304 (x0 : real -> Prop) := ~ (~ (x0 = (@EMPTY real))).
Definition term62 (x0 : real -> Prop) (x1 : real) := (@IN real x1 x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term152 (x0 : real) (x1 : real -> Prop) := real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)).
Definition term21 (x0 : real) (x1 : real -> Prop) := (fun y0 : real => (inf (@INSERT real x0 x1)) = y0) (@COND real (x1 = (@EMPTY real)) x0 (real_min x0 (inf x1))).
Definition term361 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0)) x2.
Definition term189 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term421 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le x0 x1))) /\ (~ (~ (real_le x1 x2))).
Definition term422 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term106 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : Prop) := ((@IN real x2 x0) = False) -> (False -> (real_le x1 x2) = x3) -> ((@IN real x2 x0) -> real_le x1 x2) = (False -> x3).
Definition term113 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term440 (x0 : real -> Prop) (x1 : real) := (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term248 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term271 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term74 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := (x2 x0) /\ (forall y0 : real, (@IN real y0 x1) -> x2 y0).
Definition term224 (x0 : real -> Prop) := and ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))).
Definition term465 (x0 : real) := forall y0 : real -> Prop, (@FINITE real y0) -> (inf (@INSERT real x0 y0)) = (@COND real (y0 = (@EMPTY real)) x0 (real_min x0 (inf y0))).
Definition term450 (x0 : real) := forall y0 : real -> Prop, (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> (~ (real_le x0 (inf y0))) -> (~ (real_le (inf y0) x0)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> real_le y1 y3) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> ~ (forall y1 : real -> Prop, ((@FINITE real y1) /\ (~ (y1 = (@EMPTY real)))) -> (@IN real (inf y1) y1) /\ (forall y2 : real, (@IN real y2 y1) -> real_le (inf y1) y2)).
Definition term449 (x0 : real) := forall y0 : real -> Prop, (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> (~ (real_le x0 (inf y0))) -> (~ (real_le (inf y0) x0)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> real_le y1 y3) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> (forall y1 : real -> Prop, ((@FINITE real y1) /\ (~ (y1 = (@EMPTY real)))) -> (@IN real (inf y1) y1) /\ (forall y2 : real, (@IN real y2 y1) -> real_le (inf y1) y2)) -> False.
Definition term261 (x0 : real) := forall y0 : real -> Prop, (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> (real_le x0 (inf y0)) -> (~ (forall y1 : real, (@IN real y1 y0) -> real_le x0 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> real_le y1 y3) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> ~ (forall y1 : real -> Prop, ((@FINITE real y1) /\ (~ (y1 = (@EMPTY real)))) -> (@IN real (inf y1) y1) /\ (forall y2 : real, (@IN real y2 y1) -> real_le (inf y1) y2)).
Definition term260 (x0 : real) := forall y0 : real -> Prop, (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> (real_le x0 (inf y0)) -> (~ (forall y1 : real, (@IN real y1 y0) -> real_le x0 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> real_le y1 y3) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> (forall y1 : real -> Prop, ((@FINITE real y1) /\ (~ (y1 = (@EMPTY real)))) -> (@IN real (inf y1) y1) /\ (forall y2 : real, (@IN real y2 y1) -> real_le (inf y1) y2)) -> False.
Definition term33 (x0 : real -> Prop) (x1 : real) := and ((x0 = (@EMPTY real)) -> (fun y0 : real => (inf (@INSERT real x1 x0)) = y0) x1).
Definition term337 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term349 (x0 : real -> Prop) := fun y0 : real => ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((fun y1 : real => (@IN real (inf x0) x0) /\ ((~ (@IN real y1 x0)) \/ (real_le (inf x0) y1))) y0).
Definition term341 (x0 : real -> Prop) := forall y0 : real, ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((fun y1 : real => (@IN real (inf x0) x0) /\ ((~ (@IN real y1 x0)) \/ (real_le (inf x0) y1))) y0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term38 (x0 : real) (x1 : real -> Prop) := @eq Prop ((inf (@INSERT real x0 x1)) = (@COND real (x1 = (@EMPTY real)) x0 (real_min x0 (inf x1)))).
Definition term188 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term159 (x0 : real) (x1 : real -> Prop) := (real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)) x0) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)) y0).
Definition term141 (x0 : real) (x1 : real -> Prop) := (real_le (real_min x0 (inf x1)) x0) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (real_min x0 (inf x1)) y0).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0)) x1.
Definition term233 (x0 : Prop) := (~ x0) -> False.
Definition term223 (x0 : real) (x1 : real -> Prop) (x2 : Prop) := ((@IN real x0 x1) -> (real_le (inf x1) x0) = x2) -> ((@IN real x0 x1) -> real_le (inf x1) x0) = ((@IN real x0 x1) -> x2).
Definition term111 := fun y0 : real => True.
Definition term425 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2)))).
Definition term235 (x0 : real -> Prop) (x1 : real) := ~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term142 (x0 : real) (x1 : real -> Prop) := and (@IN real (real_min x0 (inf x1)) (@INSERT real x0 x1)).
Definition term28 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) -> (inf (@INSERT real x0 x1)) = (real_min x0 (inf x1)).
Definition term226 (x0 : real) (x1 : real -> Prop) := ((@IN real x0 x1) -> (real_le (inf x1) x0) = True) -> ((@IN real x0 x1) -> real_le (inf x1) x0) = ((@IN real x0 x1) -> True).
Definition term146 (x0 : real) (x1 : real -> Prop) := @IN real (real_min x0 (inf x1)).
Definition term464 (x0 : real) (x1 : real -> Prop) := (@FINITE real x1) -> (inf (@INSERT real x0 x1)) = (@COND real (x1 = (@EMPTY real)) x0 (real_min x0 (inf x1))).
Definition term145 (x0 : real) (x1 : real -> Prop) := @COND real (real_le x0 (inf x1)) x0 (inf x1).
Definition term67 (x0 : real) (x1 : real -> Prop) := (@FINITE real (@INSERT real x0 x1)) /\ (~ ((@INSERT real x0 x1) = (@EMPTY real))).
Definition term269 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term115 (x0 : real) := (real_le x0 x0) /\ True.
Definition term83 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 (@INSERT real x1 x0)) -> real_le x1 y0.
Definition term267 (x0 : real -> Prop) := imp ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))).
Definition term20 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (inf (@INSERT real x0 x1)) = y0.
Definition term242 := forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1).
Definition term307 (x0 : real -> Prop) := (~ (@FINITE real x0)) \/ (x0 = (@EMPTY real)).
Definition term216 (x0 : real) (x1 : real -> Prop) := and (@IN real (inf x1) (@INSERT real x0 x1)).
Definition term391 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term342 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (@IN real (inf x0) x0) /\ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0))) x1.
Definition term153 (x0 : real -> Prop) (x1 : real) := real_le (@COND real (real_le x1 (inf x0)) x1 (inf x0)) x1.
Definition term70 (x0 : real) := @IN real x0 (@INSERT real x0 (@EMPTY real)).
Definition term338 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (forall y0 : real, x1 y0).
Definition term183 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((y0 = y1) \/ (@IN a0 y0 y2))) x0.
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@FINITE a0 (@INSERT a0 y0 x0)) = (@FINITE a0 x0)) x1.
Definition term410 (x0 : real -> Prop) (x1 : real) := (~ (real_le (inf x0) x1)) -> real_le (inf x0) x1.
Definition term112 := forall y0 : real, True.
Definition term64 (x0 : real) (x1 : real -> Prop) := @FINITE real (@INSERT real x0 x1).
Definition term26 (x0 : real -> Prop) := imp (~ (x0 = (@EMPTY real))).
Definition term114 (x0 : Prop) := forall y0 : real, x0.
Definition term296 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_le x1 x0)) \/ (~ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term370 (x0 : Prop) := (~ x0) -> x0.
Definition term286 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) -> real_le x1 y0) x2.
Definition term332 (x0 : real -> Prop) := fun y0 : real => (@IN real (inf x0) x0) /\ ((fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le (inf x0) y1)) y0).
Definition term126 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) -> (fun y1 : real => real_le (real_min x0 (inf x1)) y1) y0.
Definition term82 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 (@INSERT real x1 x0)) -> (fun y1 : real => real_le x1 y1) y0.
Definition term196 (x0 : real -> Prop) := (fun y0 : real -> Prop => ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) x0.
Definition term394 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term178 (x0 : real -> Prop) (x1 : real) := and ((real_le x1 (inf x0)) -> (@IN real x1 (@INSERT real x1 x0)) /\ ((real_le x1 x1) /\ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0))).
Definition term417 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2))).
Definition term12 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@INSERT a0 y1 (@EMPTY a0))) = (y0 = y1)) x0.
Definition term347 (x0 : real -> Prop) (x1 : real) := ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((fun y0 : real => (@IN real (inf x0) x0) /\ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0))) x1).
Definition term247 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term120 (x0 : real) (x1 : real -> Prop) := ((fun y0 : real => real_le (real_min x0 (inf x1)) y0) x0) /\ (forall y0 : real, (@IN real y0 x1) -> (fun y1 : real => real_le (real_min x0 (inf x1)) y1) y0).
Definition term466 := forall y0 : real, forall y1 : real -> Prop, (@FINITE real y1) -> (inf (@INSERT real y0 y1)) = (@COND real (y1 = (@EMPTY real)) y0 (real_min y0 (inf y1))).
Definition term454 := forall y0 : real, forall y1 : real -> Prop, (@FINITE real y1) -> (~ (y1 = (@EMPTY real))) -> (~ (real_le y0 (inf y1))) -> (~ (real_le (inf y1) y0)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> real_le y2 y4) -> (forall y2 : real, forall y3 : real, (real_le y2 y3) \/ (real_le y3 y2)) -> ~ (forall y2 : real -> Prop, ((@FINITE real y2) /\ (~ (y2 = (@EMPTY real)))) -> (@IN real (inf y2) y2) /\ (forall y3 : real, (@IN real y3 y2) -> real_le (inf y2) y3)).
Definition term453 := forall y0 : real, forall y1 : real -> Prop, (@FINITE real y1) -> (~ (y1 = (@EMPTY real))) -> (~ (real_le y0 (inf y1))) -> (~ (real_le (inf y1) y0)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> real_le y2 y4) -> (forall y2 : real, forall y3 : real, (real_le y2 y3) \/ (real_le y3 y2)) -> (forall y2 : real -> Prop, ((@FINITE real y2) /\ (~ (y2 = (@EMPTY real)))) -> (@IN real (inf y2) y2) /\ (forall y3 : real, (@IN real y3 y2) -> real_le (inf y2) y3)) -> False.
Definition term303 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term301 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term280 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term278 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term273 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term265 := forall y0 : real, forall y1 : real -> Prop, (@FINITE real y1) -> (~ (y1 = (@EMPTY real))) -> (real_le y0 (inf y1)) -> (~ (forall y2 : real, (@IN real y2 y1) -> real_le y0 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> real_le y2 y4) -> (forall y2 : real, forall y3 : real, (real_le y2 y3) \/ (real_le y3 y2)) -> ~ (forall y2 : real -> Prop, ((@FINITE real y2) /\ (~ (y2 = (@EMPTY real)))) -> (@IN real (inf y2) y2) /\ (forall y3 : real, (@IN real y3 y2) -> real_le (inf y2) y3)).
Definition term264 := forall y0 : real, forall y1 : real -> Prop, (@FINITE real y1) -> (~ (y1 = (@EMPTY real))) -> (real_le y0 (inf y1)) -> (~ (forall y2 : real, (@IN real y2 y1) -> real_le y0 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> real_le y2 y4) -> (forall y2 : real, forall y3 : real, (real_le y2 y3) \/ (real_le y3 y2)) -> (forall y2 : real -> Prop, ((@FINITE real y2) /\ (~ (y2 = (@EMPTY real)))) -> (@IN real (inf y2) y2) /\ (forall y3 : real, (@IN real y3 y2) -> real_le (inf y2) y3)) -> False.
Definition term227 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) -> True.
Definition term282 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) /\ (~ (real_le x1 x2)).
Definition term418 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_le x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2)))).
Definition term102 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN real x2 x0) = y0) -> (y0 -> (real_le x1 x2) = y1) -> ((@IN real x2 x0) -> real_le x1 x2) = (y0 -> y1)) x3.
Definition term244 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term97 (x0 : real -> Prop) (x1 : real) := (real_le x1 x1) /\ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term274 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term156 (x0 : real) (x1 : real -> Prop) (x2 : real) := (@IN real x2 x1) -> real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)) x2.
Definition term136 (x0 : real) (x1 : real -> Prop) (x2 : real) := (@IN real x2 x1) -> real_le (real_min x0 (inf x1)) x2.
Definition term27 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) -> (fun y0 : real => (inf (@INSERT real x0 x1)) = y0) (real_min x0 (inf x1)).
Definition term148 (x0 : real) (x1 : real -> Prop) := @IN real (real_min x0 (inf x1)) (@INSERT real x0 x1).
Definition term382 (x0 : real) (x1 : real -> Prop) := (x1 = (@EMPTY real)) \/ ((real_le (inf x1) x0) \/ ((~ (@FINITE real x1)) \/ (~ (@IN real x0 x1)))).
Definition term364 (x0 : real -> Prop) (x1 : real) := ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((~ (@IN real x1 x0)) \/ (real_le (inf x0) x1)).
Definition term193 (x0 : real) := or (x0 = x0).
Definition term253 (x0 : real -> Prop) (x1 : real) := (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term252 (x0 : real -> Prop) (x1 : real) := (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 (@INSERT a0 x0 y0)) -> x1 y1) = ((x1 x0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> x1 y1)).
Definition term285 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (@IN real y1 x0) -> real_le x1 y1) y0).
Definition term340 (x0 : real -> Prop) := ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ (forall y0 : real, (fun y1 : real => (@IN real (inf x0) x0) /\ ((~ (@IN real y1 x0)) \/ (real_le (inf x0) y1))) y0).
Definition term179 (x0 : real) (x1 : real -> Prop) := ((real_le x0 (inf x1)) -> (@IN real x0 (@INSERT real x0 x1)) /\ ((real_le x0 x0) /\ (forall y0 : real, (@IN real y0 x1) -> real_le x0 y0))) /\ ((~ (real_le x0 (inf x1))) -> (@IN real (inf x1) (@INSERT real x0 x1)) /\ ((real_le (inf x1) x0) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (inf x1) y0))).
Definition term362 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, (((~ (@FINITE real y0)) \/ (y0 = (@EMPTY real))) \/ (@IN real (inf y0) y0)) /\ (((~ (@FINITE real y0)) \/ (y0 = (@EMPTY real))) \/ ((~ (@IN real y1 y0)) \/ (real_le (inf y0) y1)))) x0.
Definition term17 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term339 (x0 : Prop) (x1 : real -> Prop) := forall y0 : real, x0 \/ (x1 y0).
Definition term378 (x0 : real -> Prop) (x1 : real) := (~ (@FINITE real x0)) \/ ((~ (@IN real x1 x0)) \/ (real_le (inf x0) x1)).
Definition term376 (x0 : real -> Prop) (x1 : real) := (x0 = (@EMPTY real)) \/ ((~ (@FINITE real x0)) \/ ((~ (@IN real x1 x0)) \/ (real_le (inf x0) x1))).
Definition term368 (x0 : real -> Prop) := ~ (@FINITE real x0).
Definition term208 (x0 : real -> Prop) := @IN real (inf x0) x0.
Definition term88 (x0 : real) := and ((fun y0 : real => real_le x0 y0) x0).
Definition term130 (x0 : real) (x1 : real -> Prop) := @eq Prop (forall y0 : real, (@IN real y0 (@INSERT real x0 x1)) -> real_le (real_min x0 (inf x1)) y0).
Definition term129 (x0 : real) (x1 : real -> Prop) := @eq Prop (forall y0 : real, (@IN real y0 (@INSERT real x0 x1)) -> (fun y1 : real => real_le (real_min x0 (inf x1)) y1) y0).
Definition term86 (x0 : real -> Prop) (x1 : real) := @eq Prop (forall y0 : real, (@IN real y0 (@INSERT real x1 x0)) -> real_le x1 y0).
Definition term85 (x0 : real -> Prop) (x1 : real) := @eq Prop (forall y0 : real, (@IN real y0 (@INSERT real x1 x0)) -> (fun y1 : real => real_le x1 y1) y0).
Definition term98 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term68 (x0 : real -> Prop) (x1 : real) := (@IN real x1 (@INSERT real x1 x0)) /\ (forall y0 : real, (@IN real y0 (@INSERT real x1 x0)) -> real_le x1 y0).
Definition term117 (x0 : real) (x1 : real -> Prop) := ((@FINITE real (@INSERT real x0 x1)) /\ (~ ((@INSERT real x0 x1) = (@EMPTY real)))) -> ((inf (@INSERT real x0 x1)) = (real_min x0 (inf x1))) = ((@IN real (real_min x0 (inf x1)) (@INSERT real x0 x1)) /\ (forall y0 : real, (@IN real y0 (@INSERT real x0 x1)) -> real_le (real_min x0 (inf x1)) y0)).
Definition term318 := forall y0 : real -> Prop, ((~ (@FINITE real y0)) \/ (y0 = (@EMPTY real))) \/ ((@IN real (inf y0) y0) /\ (forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le (inf y0) y1))).
Definition term163 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) /\ ((real_le y0 x0) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)).
Definition term230 (x0 : real) (x1 : real -> Prop) := (real_le (inf x1) x0) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (inf x1) y0).
Definition term105 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : Prop) (x4 : Prop) := ((@IN real x2 x0) = x3) -> (x3 -> (real_le x1 x2) = x4) -> ((@IN real x2 x0) -> real_le x1 x2) = (x3 -> x4).
Definition term81 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 (@INSERT real x1 x0)) -> real_le x1 x2.
Definition term174 (x0 : real) (x1 : real -> Prop) := imp (real_le x0 (inf x1)).
Definition term434 (x0 : real -> Prop) (x1 : real) := (~ (real_le (inf x0) x1)) -> False.
Definition term37 (x0 : real) (x1 : real -> Prop) := @eq Prop ((fun y0 : real => (inf (@INSERT real x0 x1)) = y0) (@COND real (x1 = (@EMPTY real)) x0 (real_min x0 (inf x1)))).
Definition term377 (x0 : real) (x1 : real -> Prop) := (real_le (inf x1) x0) \/ (~ (@IN real x0 x1)).
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ~ ((@INSERT a0 x0 y0) = (@EMPTY a0))) x1.
Definition term436 (x0 : real -> Prop) (x1 : real) := ((@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term237 (x0 : real -> Prop) (x1 : real) := ((@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term22 (x0 : real) (x1 : real -> Prop) := ((x1 = (@EMPTY real)) -> (fun y0 : real => (inf (@INSERT real x0 x1)) = y0) x0) /\ ((~ (x1 = (@EMPTY real))) -> (fun y0 : real => (inf (@INSERT real x0 x1)) = y0) (real_min x0 (inf x1))).
Definition term241 := ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term137 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (@IN real y0 x1) -> (fun y1 : real => real_le (real_min x0 (inf x1)) y1) y0.
Definition term309 (x0 : real -> Prop) (x1 : real) := (~ (@IN real x1 x0)) \/ (real_le (inf x0) x1).
Definition term29 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (inf (@INSERT real x1 x0)) = y0) x1.
Definition term311 (x0 : real -> Prop) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le (inf x0) y0).
Definition term385 (x0 : real) (x1 : real -> Prop) := (~ (@FINITE real x1)) \/ ((x1 = (@EMPTY real)) \/ (~ (@IN real x0 x1))).
Definition term191 (x0 : real) (x1 : real) (x2 : real -> Prop) := (x1 = x0) \/ (@IN real x1 x2).
Definition term76 (x0 : real -> Prop) (x1 : real) := ((fun y0 : real => real_le x1 y0) x1) /\ (forall y0 : real, (@IN real y0 x0) -> (fun y1 : real => real_le x1 y1) y0).
Definition term375 (x0 : real) (x1 : real -> Prop) := ~ (@IN real x0 x1).
Definition term460 (x0 : real -> Prop) (x1 : real) := (~ (real_le x1 (inf x0))) -> real_le (inf x0) x1.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term390 (x0 : real) (x1 : real -> Prop) := (~ (@FINITE real x1)) \/ (~ (@IN real x0 x1)).
Definition term387 (x0 : real -> Prop) (x1 : real) := or (real_le (inf x0) x1).
Definition term333 (x0 : real -> Prop) := fun y0 : real => (@IN real (inf x0) x0) /\ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0)).
Definition term406 (x0 : real) (x1 : real -> Prop) := (@FINITE real x1) /\ ((~ (x1 = (@EMPTY real))) /\ (@IN real x0 x1)).
Definition term161 (x0 : real) (x1 : real -> Prop) (x2 : Prop) (x3 : real) (x4 : real) := (fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) /\ ((real_le y0 x0) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1))) (@COND real x2 x3 x4).
Definition term154 (x0 : real -> Prop) (x1 : real) := and (real_le (@COND real (real_le x1 (inf x0)) x1 (inf x0)) x1).
Definition term134 (x0 : real -> Prop) (x1 : real) := and (real_le (real_min x1 (inf x0)) x1).
Definition term324 (x0 : real -> Prop) := forall y0 : real, (@IN real (inf x0) x0) /\ ((fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le (inf x0) y1)) y0).
Definition term65 (x0 : real) (x1 : real -> Prop) := and (@FINITE real (@INSERT real x0 x1)).
Definition term155 (x0 : real) (x1 : real -> Prop) (x2 : real) := real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)) x2.
Definition term151 (x0 : real) (x1 : real -> Prop) := real_le (real_min x0 (inf x1)).
Definition term369 (x0 : real) (x1 : real -> Prop) := (~ (real_le x0 (inf x1))) -> real_le x0 (inf x1).
Definition term167 (x0 : real) (x1 : real -> Prop) := (fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) /\ ((real_le y0 x0) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1))) (inf x1).
Definition term9 (x0 : real) (x1 : real) := (fun y0 : real => (real_min x0 y0) = (@COND real (real_le x0 y0) x0 y0)) x1.
Definition term393 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term127 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) -> real_le (real_min x0 (inf x1)) y0.
Definition term201 (x0 : real -> Prop) (x1 : real) := (@IN real x1 x0) -> real_le (inf x0) x1.
Definition term195 (x0 : real -> Prop) (x1 : real) := True /\ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term404 (x0 : real -> Prop) := and (~ (x0 = (@EMPTY real))).
Definition term295 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_le x1 x0) /\ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term225 (x0 : real) (x1 : real -> Prop) := ((@FINITE real x1) /\ (~ (x1 = (@EMPTY real)))) /\ (@IN real x0 x1).
Definition term24 (x0 : real) (x1 : real -> Prop) := (fun y0 : real => (inf (@INSERT real x0 x1)) = y0) (real_min x0 (inf x1)).
Definition term35 (x0 : real) (x1 : real -> Prop) := ((x1 = (@EMPTY real)) -> (inf (@INSERT real x0 x1)) = x0) /\ ((~ (x1 = (@EMPTY real))) -> (inf (@INSERT real x0 x1)) = (real_min x0 (inf x1))).
Definition term132 (x0 : real -> Prop) (x1 : real) := real_le (real_min x1 (inf x0)) x1.
Definition term354 (x0 : real -> Prop) (x1 : real) := (((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ (@IN real (inf x0) x0)) /\ (((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((~ (@IN real x1 x0)) \/ (real_le (inf x0) x1))).
Definition term144 (x0 : real) (x1 : real) := @IN real x0 (@INSERT real x1 (@EMPTY real)).
Definition term305 (x0 : real -> Prop) := or (~ (@FINITE real x0)).
Definition term371 (x0 : real -> Prop) := (~ (@FINITE real x0)) -> @FINITE real x0.
Definition term220 (x0 : real -> Prop) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((@IN real x1 x0) = x2) -> (x2 -> (real_le (inf x0) x1) = y0) -> ((@IN real x1 x0) -> real_le (inf x0) x1) = (x2 -> y0)) x3.
Definition term79 (x0 : real) (x1 : real) (x2 : real -> Prop) := imp (@IN real x0 (@INSERT real x1 x2)).
Definition term348 (x0 : real -> Prop) (x1 : real) := ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((@IN real (inf x0) x0) /\ ((~ (@IN real x1 x0)) \/ (real_le (inf x0) x1))).
Definition term221 (x0 : real -> Prop) (x1 : real) (x2 : Prop) (x3 : Prop) := ((@IN real x1 x0) = x2) -> (x2 -> (real_le (inf x0) x1) = x3) -> ((@IN real x1 x0) -> real_le (inf x0) x1) = (x2 -> x3).
Definition term94 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le x1 y0.
Definition term441 (x0 : real -> Prop) (x1 : real) := (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term80 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 (@INSERT real x1 x0)) -> (fun y0 : real => real_le x1 y0) x2.
Definition term426 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term379 (x0 : real) (x1 : real -> Prop) := (~ (@FINITE real x1)) \/ ((real_le (inf x1) x0) \/ (~ (@IN real x0 x1))).
Definition term23 (x0 : real) (x1 : real -> Prop) := real_min x0 (inf x1).
Definition term39 (x0 : real -> Prop) := ~ (x0 = (@EMPTY real)).
Definition term166 (x0 : real) (x1 : real -> Prop) := real_le x0 (inf x1).
Definition term300 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term277 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term272 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term110 (x0 : real) (x1 : real) := False -> real_le x0 x1.
Definition term322 (x0 : Prop) (x1 : real -> Prop) := forall y0 : real, x0 /\ (x1 y0).
Definition term51 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, ~ ((@INSERT a0 x0 y0) = (@EMPTY a0)).
Definition term284 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term240 := (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term287 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (@IN real y0 x0) -> real_le x1 y0) x2).
Definition term461 (x0 : real -> Prop) (x1 : real) := (real_le (inf x0) x1) -> False.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term175 (x0 : real -> Prop) (x1 : real) := (real_le x1 (inf x0)) -> (fun y0 : real => (@IN real y0 (@INSERT real x1 x0)) /\ ((real_le y0 x1) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1))) x1.
Definition term455 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, (real_min y0 y1) = (@COND real (real_le y0 y1) y0 y1)) x0.
Definition term66 (x0 : real) (x1 : real -> Prop) := ~ ((@INSERT real x0 x1) = (@EMPTY real)).
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((@INSERT a0 x0 x1) = (@EMPTY a0)).
Definition term211 (x0 : real) (x1 : real -> Prop) := ((inf x1) = x0) \/ (@IN real (inf x1) x1).
Definition term90 (x0 : real) (x1 : real -> Prop) := imp (@IN real x0 x1).
Definition term18 (x0 : real) (x1 : real -> Prop) (x2 : Prop) (x3 : real) (x4 : real) := (fun y0 : real => (inf (@INSERT real x0 x1)) = y0) (@COND real x2 x3 x4).
Definition term162 (x0 : real) (x1 : Prop) (x2 : real) (x3 : real -> Prop) (x4 : real) := (x1 -> (fun y0 : real => (@IN real y0 (@INSERT real x2 x3)) /\ ((real_le y0 x2) /\ (forall y1 : real, (@IN real y1 x3) -> real_le y0 y1))) x0) /\ ((~ x1) -> (fun y0 : real => (@IN real y0 (@INSERT real x2 x3)) /\ ((real_le y0 x2) /\ (forall y1 : real, (@IN real y1 x3) -> real_le y0 y1))) x4).
Definition term19 (x0 : real) (x1 : Prop) (x2 : real) (x3 : real -> Prop) (x4 : real) := (x1 -> (fun y0 : real => (inf (@INSERT real x2 x3)) = y0) x0) /\ ((~ x1) -> (fun y0 : real => (inf (@INSERT real x2 x3)) = y0) x4).
Definition term58 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @FINITE a0 (@INSERT a0 x0 x1).
Definition term194 (x0 : real) (x1 : real -> Prop) := True \/ (@IN real x0 x1).
Definition term427 (x0 : real) (x1 : real -> Prop) (x2 : real) := (real_le x0 (inf x1)) /\ (real_le (inf x1) x2).
Definition term334 (x0 : real -> Prop) := forall y0 : real, (@IN real (inf x0) x0) /\ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0)).
Definition term96 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le x1 y0.
Definition term403 (x0 : real) (x1 : real -> Prop) := ~ (~ (@IN real x0 x1)).
Definition term313 (x0 : real -> Prop) := or (~ ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real))))).
Definition term294 (x0 : real) (x1 : real) (x2 : real) := or ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term351 (x0 : real -> Prop) := forall y0 : real, ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((@IN real (inf x0) x0) /\ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0))).
Definition term59 (x0 : real) (x1 : real -> Prop) := (fun y0 : real -> Prop => ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> ((inf y0) = x0) = ((@IN real x0 y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le x0 y1))) x1.
Definition term32 (x0 : real -> Prop) (x1 : real) := (x0 = (@EMPTY real)) -> (inf (@INSERT real x1 x0)) = x1.
Definition term128 (x0 : real) (x1 : real -> Prop) := forall y0 : real, (@IN real y0 (@INSERT real x0 x1)) -> real_le (real_min x0 (inf x1)) y0.
Definition term321 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (forall y0 : real, x1 y0).
Definition term330 (x0 : real -> Prop) (x1 : real) := (@IN real (inf x0) x0) /\ ((fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le (inf x0) y0)) x1).
Definition term234 (x0 : real -> Prop) (x1 : real) := (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> False.
Definition term344 (x0 : real -> Prop) := forall y0 : real, (fun y1 : real => (@IN real (inf x0) x0) /\ ((~ (@IN real y1 x0)) \/ (real_le (inf x0) y1))) y0.
Definition term327 (x0 : real -> Prop) := forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le (inf x0) y1)) y0.
Definition term212 (x0 : real -> Prop) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (@IN real (inf x0) x0) = True.
Definition term270 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term219 (x0 : real -> Prop) (x1 : real) (x2 : Prop) := forall y0 : Prop, ((@IN real x1 x0) = x2) -> (x2 -> (real_le (inf x0) x1) = y0) -> ((@IN real x1 x0) -> real_le (inf x0) x1) = (x2 -> y0).
Definition term103 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : Prop) := forall y0 : Prop, ((@IN real x2 x0) = x3) -> (x3 -> (real_le x1 x2) = y0) -> ((@IN real x2 x0) -> real_le x1 x2) = (x3 -> y0).
Definition term99 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term320 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 /\ (x1 y0).
Definition term121 (x0 : real) (x1 : real -> Prop) := fun y0 : real => real_le (real_min x0 (inf x1)) y0.
Definition term386 (x0 : real) (x1 : real -> Prop) := (x1 = (@EMPTY real)) \/ ((~ (@FINITE real x1)) \/ (~ (@IN real x0 x1))).
Definition term250 (x0 : real -> Prop) (x1 : real) := (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term438 (x0 : real -> Prop) (x1 : real) := (((@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> ((@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term239 (x0 : real -> Prop) (x1 : real) := (((@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> ((@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term458 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term197 (x0 : real -> Prop) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (@IN real (inf x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0).
Definition term215 (x0 : real -> Prop) (x1 : real) := ((inf x0) = x1) \/ True.
Definition term187 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0))) x2.
Definition term210 (x0 : real) (x1 : real -> Prop) := @IN real (inf x1) (@INSERT real x0 x1).
Definition term389 (x0 : real) (x1 : real -> Prop) := (real_le (inf x1) x0) \/ ((x1 = (@EMPTY real)) \/ ((~ (@FINITE real x1)) \/ (~ (@IN real x0 x1)))).
Definition term310 (x0 : real -> Prop) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le (inf x0) y0).
Definition term177 (x0 : real -> Prop) (x1 : real) := and ((real_le x1 (inf x0)) -> (fun y0 : real => (@IN real y0 (@INSERT real x1 x0)) /\ ((real_le y0 x1) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1))) x1).
Definition term71 (x0 : real) (x1 : real -> Prop) := and (@IN real x0 (@INSERT real x0 x1)).
Definition term147 (x0 : real) (x1 : real -> Prop) := @IN real (@COND real (real_le x0 (inf x1)) x0 (inf x1)).
Definition term414 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term206 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term217 (x0 : real -> Prop) (x1 : real) := forall y0 : Prop, forall y1 : Prop, ((@IN real x1 x0) = y0) -> (y0 -> (real_le (inf x0) x1) = y1) -> ((@IN real x1 x0) -> real_le (inf x0) x1) = (y0 -> y1).
Definition term101 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : Prop, forall y1 : Prop, ((@IN real x2 x0) = y0) -> (y0 -> (real_le x1 x2) = y1) -> ((@IN real x2 x0) -> real_le x1 x2) = (y0 -> y1).
Definition term100 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term124 (x0 : real) (x1 : real -> Prop) (x2 : real) := (@IN real x2 (@INSERT real x0 x1)) -> (fun y0 : real => real_le (real_min x0 (inf x1)) y0) x2.
Definition term360 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1)) x1.
Definition term423 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term331 (x0 : real -> Prop) (x1 : real) := (@IN real (inf x0) x0) /\ ((~ (@IN real x1 x0)) \/ (real_le (inf x0) x1)).
Definition term419 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x2)))) -> real_le x1 x2.
Definition term131 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => real_le (real_min x1 (inf x0)) y0) x1.
Definition term402 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) /\ (~ (~ (@IN real x0 x1))).
Definition term181 (x0 : real) (x1 : real -> Prop) := @eq Prop ((@IN real (@COND real (real_le x0 (inf x1)) x0 (inf x1)) (@INSERT real x0 x1)) /\ ((real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)) x0) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)) y0))).
Definition term207 (x0 : real -> Prop) (x1 : real) := (((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) /\ (@IN real x1 x0)) -> (real_le (inf x0) x1) = True.
Definition term463 (x0 : real) (x1 : real -> Prop) := (fun y0 : real -> Prop => (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> (~ (real_le x0 (inf y0))) -> (~ (real_le (inf y0) x0)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> real_le y1 y3) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> (forall y1 : real -> Prop, ((@FINITE real y1) /\ (~ (y1 = (@EMPTY real)))) -> (@IN real (inf y1) y1) /\ (forall y2 : real, (@IN real y2 y1) -> real_le (inf y1) y2)) -> False) x1.
Definition term433 (x0 : real) (x1 : real -> Prop) := (fun y0 : real -> Prop => (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> (real_le x0 (inf y0)) -> (~ (forall y1 : real, (@IN real y1 y0) -> real_le x0 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> real_le y1 y3) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> (forall y1 : real -> Prop, ((@FINITE real y1) /\ (~ (y1 = (@EMPTY real)))) -> (@IN real (inf y1) y1) /\ (forall y2 : real, (@IN real y2 y1) -> real_le (inf y1) y2)) -> False) x1.
Definition term355 (x0 : real -> Prop) := fun y0 : real => (((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ (@IN real (inf x0) x0)) /\ (((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0))).
Definition term298 (x0 : real) (x1 : real) := fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 x1)) -> x2 y0.
Definition term397 (x0 : real) (x1 : real -> Prop) := (x1 = (@EMPTY real)) \/ (~ (@IN real x0 x1)).
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ ((@INSERT a0 x0 x1) = (@EMPTY a0))) -> ((@INSERT a0 x0 x1) = (@EMPTY a0)) = False.
Definition term222 (x0 : real) (x1 : real -> Prop) (x2 : Prop) := ((@IN real x0 x1) = (@IN real x0 x1)) -> ((@IN real x0 x1) -> (real_le (inf x1) x0) = x2) -> ((@IN real x0 x1) -> real_le (inf x1) x0) = ((@IN real x0 x1) -> x2).
Definition term104 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN real x2 x0) = x3) -> (x3 -> (real_le x1 x2) = y0) -> ((@IN real x2 x0) -> real_le x1 x2) = (x3 -> y0)) x4.
Definition term413 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ (~ (real_le x1 x2)).
Definition term312 (x0 : real -> Prop) := (@IN real (inf x0) x0) /\ (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le (inf x0) y0)).
Definition term198 (x0 : real -> Prop) := (@IN real (inf x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0).
Definition term157 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (@IN real y0 x1) -> real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)) y0.
Definition term138 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (@IN real y0 x1) -> real_le (real_min x0 (inf x1)) y0.
Definition term229 (x0 : real -> Prop) (x1 : real) := and (real_le (inf x0) x1).
Definition term34 (x0 : real -> Prop) (x1 : real) := and ((x0 = (@EMPTY real)) -> (inf (@INSERT real x1 x0)) = x1).
Definition term358 := forall y0 : real -> Prop, forall y1 : real, (((~ (@FINITE real y0)) \/ (y0 = (@EMPTY real))) \/ (@IN real (inf y0) y0)) /\ (((~ (@FINITE real y0)) \/ (y0 = (@EMPTY real))) \/ ((~ (@IN real y1 y0)) \/ (real_le (inf y0) y1))).
Definition term353 := forall y0 : real -> Prop, forall y1 : real, ((~ (@FINITE real y0)) \/ (y0 = (@EMPTY real))) \/ ((@IN real (inf y0) y0) /\ ((~ (@IN real y1 y0)) \/ (real_le (inf y0) y1))).
Definition term204 (x0 : real -> Prop) (x1 : real) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (@IN real x1 x0) -> (real_le (inf x0) x1) = True.
Definition term411 (x0 : real -> Prop) (x1 : real) := ~ (real_le (inf x0) x1).
Definition term8 (x0 : real) := forall y0 : real, (real_min x0 y0) = (@COND real (real_le x0 y0) x0 y0).
Definition term266 (x0 : real -> Prop) := and (@IN real (inf x0) x0).
Definition term10 (x0 : real) (x1 : real) := @COND real (real_le x0 x1) x0 x1.
Definition term388 (x0 : real) (x1 : real -> Prop) := (real_le (inf x1) x0) \/ ((~ (@FINITE real x1)) \/ ((x1 = (@EMPTY real)) \/ (~ (@IN real x0 x1)))).
Definition term123 (x0 : real) (x1 : real -> Prop) (x2 : real) := real_le (real_min x0 (inf x1)) x2.
Definition term446 (x0 : real -> Prop) (x1 : real) := (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term435 (x0 : real -> Prop) (x1 : real) := (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term257 (x0 : real -> Prop) (x1 : real) := (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term236 (x0 : real -> Prop) (x1 : real) := (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term214 (x0 : real -> Prop) (x1 : real) := or ((inf x0) = x1).
Definition term392 (x0 : real -> Prop) (x1 : real) := (~ ((~ (@FINITE real x0)) \/ ((x0 = (@EMPTY real)) \/ (~ (@IN real x1 x0))))) -> real_le (inf x0) x1.
Definition term317 := fun y0 : real -> Prop => ((~ (@FINITE real y0)) \/ (y0 = (@EMPTY real))) \/ ((@IN real (inf y0) y0) /\ (forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le (inf y0) y1))).
Definition term125 (x0 : real) (x1 : real -> Prop) (x2 : real) := (@IN real x2 (@INSERT real x0 x1)) -> real_le (real_min x0 (inf x1)) x2.
Definition term87 (x0 : real) := (fun y0 : real => real_le x0 y0) x0.
Definition term118 (x0 : real) (x1 : real -> Prop) := (@IN real (real_min x0 (inf x1)) (@INSERT real x0 x1)) /\ (forall y0 : real, (@IN real y0 (@INSERT real x0 x1)) -> real_le (real_min x0 (inf x1)) y0).
Definition term302 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term279 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term192 (x0 : real) (x1 : real -> Prop) := (x0 = x0) \/ (@IN real x0 x1).
Definition term11 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term357 := fun y0 : real -> Prop => forall y1 : real, (((~ (@FINITE real y0)) \/ (y0 = (@EMPTY real))) \/ (@IN real (inf y0) y0)) /\ (((~ (@FINITE real y0)) \/ (y0 = (@EMPTY real))) \/ ((~ (@IN real y1 y0)) \/ (real_le (inf y0) y1))).
Definition term352 := fun y0 : real -> Prop => forall y1 : real, ((~ (@FINITE real y0)) \/ (y0 = (@EMPTY real))) \/ ((@IN real (inf y0) y0) /\ ((~ (@IN real y1 y0)) \/ (real_le (inf y0) y1))).
Definition term363 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ (@IN real (inf x0) x0)) /\ (((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0)))) x1.
Definition term63 (x0 : real -> Prop) (x1 : real) := ((@FINITE real (@INSERT real x1 x0)) /\ (~ ((@INSERT real x1 x0) = (@EMPTY real)))) -> ((inf (@INSERT real x1 x0)) = x1) = ((@IN real x1 (@INSERT real x1 x0)) /\ (forall y0 : real, (@IN real y0 (@INSERT real x1 x0)) -> real_le x1 y0)).
Definition term190 (x0 : real) (x1 : real) (x2 : real -> Prop) := @IN real x0 (@INSERT real x1 x2).
Definition term384 (x0 : real) (x1 : real -> Prop) := @eq Prop ((x1 = (@EMPTY real)) \/ ((real_le (inf x1) x0) \/ ((~ (@FINITE real x1)) \/ (~ (@IN real x0 x1))))).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term439 (x0 : real -> Prop) (x1 : real) := imp (~ (real_le (inf x0) x1)).
Definition term366 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term109 (x0 : real -> Prop) (x1 : real) (x2 : real) := (False -> (real_le x1 x2) = (real_le x1 x2)) -> ((@IN real x2 x0) -> real_le x1 x2) = (False -> real_le x1 x2).
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (x2 x0) /\ (forall y0 : a0, (@IN a0 y0 x1) -> x2 y0).
Definition term408 (x0 : real) (x1 : real -> Prop) := imp ((@FINITE real x1) /\ ((~ (x1 = (@EMPTY real))) /\ (@IN real x0 x1))).
Definition term164 (x0 : real) (x1 : real -> Prop) := (fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) /\ ((real_le y0 x0) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1))) (@COND real (real_le x0 (inf x1)) x0 (inf x1)).
Definition term172 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (@IN real y0 (@INSERT real x1 x0)) /\ ((real_le y0 x1) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1))) x1.
Definition term73 (x0 : real) (x1 : real -> Prop) (x2 : real -> Prop) := forall y0 : real, (@IN real y0 (@INSERT real x0 x1)) -> x2 y0.
Definition term290 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (@IN real y0 x0) /\ (~ (real_le x1 y0)).
Definition term346 (x0 : real -> Prop) := @eq Prop (((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ (forall y0 : real, (@IN real (inf x0) x0) /\ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0)))).
Definition term345 (x0 : real -> Prop) := @eq Prop (((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ (forall y0 : real, (fun y1 : real => (@IN real (inf x0) x0) /\ ((~ (@IN real y1 x0)) \/ (real_le (inf x0) y1))) y0)).
Definition term13 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0).
Definition term420 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term276 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term84 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 (@INSERT real x1 x0)) -> real_le x1 y0.
Definition term228 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) -> real_le (inf x0) y0.
Definition term16 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term203 (x0 : real -> Prop) (x1 : real) := (@IN real x1 x0) -> (real_le (inf x0) x1) = True.
Definition term445 (x0 : real -> Prop) (x1 : real) := (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term444 (x0 : real -> Prop) (x1 : real) := (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term91 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) -> (fun y0 : real => real_le x1 y0) x2.
Definition term343 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => (@IN real (inf x0) x0) /\ ((~ (@IN real y1 x0)) \/ (real_le (inf x0) y1))) y0.
Definition term61 (x0 : real -> Prop) := (@FINITE real x0) /\ (~ (x0 = (@EMPTY real))).
Definition term308 (x0 : real -> Prop) := ~ ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))).
Definition term245 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term424 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term399 (x0 : real -> Prop) := ~ (~ (@FINITE real x0)).
Definition term149 (x0 : real) (x1 : real -> Prop) := @IN real (@COND real (real_le x0 (inf x1)) x0 (inf x1)) (@INSERT real x0 x1).
Definition term329 (x0 : real -> Prop) := @eq Prop ((@IN real (inf x0) x0) /\ (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le (inf x0) y0))).
Definition term328 (x0 : real -> Prop) := @eq Prop ((@IN real (inf x0) x0) /\ (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le (inf x0) y1)) y0)).
Definition term326 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le (inf x0) y1)) y0.
Definition term297 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term356 (x0 : real -> Prop) := forall y0 : real, (((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ (@IN real (inf x0) x0)) /\ (((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0))).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term180 (x0 : real) (x1 : real -> Prop) := @eq Prop ((fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) /\ ((real_le y0 x0) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1))) (@COND real (real_le x0 (inf x1)) x0 (inf x1))).
Definition term374 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) -> @IN real x0 x1.
Definition term288 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (@IN real y1 x0) -> real_le x1 y1) y0).
Definition term160 (x0 : real) (x1 : real -> Prop) := (@IN real (@COND real (real_le x0 (inf x1)) x0 (inf x1)) (@INSERT real x0 x1)) /\ ((real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)) x0) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (@COND real (real_le x0 (inf x1)) x0 (inf x1)) y0)).
Definition term143 (x0 : real) (x1 : real -> Prop) := (@IN real (real_min x0 (inf x1)) (@INSERT real x0 x1)) /\ ((real_le (real_min x0 (inf x1)) x0) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (real_min x0 (inf x1)) y0)).
Definition term30 (x0 : real -> Prop) := imp (x0 = (@EMPTY real)).
Definition term135 (x0 : real) (x1 : real -> Prop) (x2 : real) := (@IN real x2 x1) -> (fun y0 : real => real_le (real_min x0 (inf x1)) y0) x2.
Definition term169 (x0 : real) (x1 : real -> Prop) := imp (~ (real_le x0 (inf x1))).
Definition term396 (x0 : real) (x1 : real -> Prop) := (~ (~ (@FINITE real x1))) /\ (~ ((x1 = (@EMPTY real)) \/ (~ (@IN real x0 x1)))).
Definition term209 (x0 : real -> Prop) := (~ (x0 = (@EMPTY real))) -> (x0 = (@EMPTY real)) = False.
Definition term42 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term256 (x0 : real -> Prop) := imp (@FINITE real x0).
Definition term405 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) /\ (@IN real x0 x1).
Definition term107 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : Prop) := (False -> (real_le x1 x2) = x3) -> ((@IN real x2 x0) -> real_le x1 x2) = (False -> x3).
Definition term401 (x0 : real) (x1 : real -> Prop) := ~ ((x1 = (@EMPTY real)) \/ (~ (@IN real x0 x1))).
Definition term92 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) -> real_le x1 x2.
Definition term213 (x0 : real -> Prop) := and (@FINITE real x0).
Definition term314 (x0 : real -> Prop) := or ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))).
Definition term168 (x0 : real) (x1 : real -> Prop) := (@IN real (inf x1) (@INSERT real x0 x1)) /\ ((real_le (inf x1) x0) /\ (forall y0 : real, (@IN real y0 x1) -> real_le (inf x1) y0)).
Definition term437 (x0 : real -> Prop) (x1 : real) := (((@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term238 (x0 : real -> Prop) (x1 : real) := (((@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False) -> (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> (real_le x1 (inf x0)) -> (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term457 (x0 : real) (x1 : real -> Prop) := (real_le x0 (inf x1)) -> ~ (real_le x0 (inf x1)).
Definition term133 (x0 : real -> Prop) (x1 : real) := and ((fun y0 : real => real_le (real_min x1 (inf x0)) y0) x1).
Definition term119 (x0 : real) (x1 : real -> Prop) := forall y0 : real, (@IN real y0 (@INSERT real x0 x1)) -> (fun y1 : real => real_le (real_min x0 (inf x1)) y1) y0.
Definition term75 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 (@INSERT real x1 x0)) -> (fun y1 : real => real_le x1 y1) y0.
Definition term350 (x0 : real -> Prop) := fun y0 : real => ((~ (@FINITE real x0)) \/ (x0 = (@EMPTY real))) \/ ((@IN real (inf x0) x0) /\ ((~ (@IN real y0 x0)) \/ (real_le (inf x0) y0))).
Definition term395 (x0 : real) (x1 : real -> Prop) := ~ ((~ (@FINITE real x1)) \/ ((x1 = (@EMPTY real)) \/ (~ (@IN real x0 x1)))).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 (@INSERT a0 y1 y2)) -> y0 y3) = ((y0 y1) /\ (forall y3 : a0, (@IN a0 y3 y2) -> y0 y3))) x0.
Definition term325 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le (inf x0) y0)) x1.
Definition term380 (x0 : real) (x1 : real -> Prop) := (real_le (inf x1) x0) \/ ((~ (@FINITE real x1)) \/ (~ (@IN real x0 x1))).
Definition term323 (x0 : real -> Prop) := (@IN real (inf x0) x0) /\ (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le (inf x0) y1)) y0).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term275 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term116 (x0 : real) := (@IN real x0 (@INSERT real x0 (@EMPTY real))) /\ (real_le x0 x0).
Definition term139 (x0 : real) (x1 : real -> Prop) := forall y0 : real, (@IN real y0 x1) -> (fun y1 : real => real_le (real_min x0 (inf x1)) y1) y0.
Definition term95 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> (fun y1 : real => real_le x1 y1) y0.
Definition term452 := fun y0 : real => forall y1 : real -> Prop, (@FINITE real y1) -> (~ (y1 = (@EMPTY real))) -> (~ (real_le y0 (inf y1))) -> (~ (real_le (inf y1) y0)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> real_le y2 y4) -> (forall y2 : real, forall y3 : real, (real_le y2 y3) \/ (real_le y3 y2)) -> ~ (forall y2 : real -> Prop, ((@FINITE real y2) /\ (~ (y2 = (@EMPTY real)))) -> (@IN real (inf y2) y2) /\ (forall y3 : real, (@IN real y3 y2) -> real_le (inf y2) y3)).
Definition term451 := fun y0 : real => forall y1 : real -> Prop, (@FINITE real y1) -> (~ (y1 = (@EMPTY real))) -> (~ (real_le y0 (inf y1))) -> (~ (real_le (inf y1) y0)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> real_le y2 y4) -> (forall y2 : real, forall y3 : real, (real_le y2 y3) \/ (real_le y3 y2)) -> (forall y2 : real -> Prop, ((@FINITE real y2) /\ (~ (y2 = (@EMPTY real)))) -> (@IN real (inf y2) y2) /\ (forall y3 : real, (@IN real y3 y2) -> real_le (inf y2) y3)) -> False.
Definition term263 := fun y0 : real => forall y1 : real -> Prop, (@FINITE real y1) -> (~ (y1 = (@EMPTY real))) -> (real_le y0 (inf y1)) -> (~ (forall y2 : real, (@IN real y2 y1) -> real_le y0 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> real_le y2 y4) -> (forall y2 : real, forall y3 : real, (real_le y2 y3) \/ (real_le y3 y2)) -> ~ (forall y2 : real -> Prop, ((@FINITE real y2) /\ (~ (y2 = (@EMPTY real)))) -> (@IN real (inf y2) y2) /\ (forall y3 : real, (@IN real y3 y2) -> real_le (inf y2) y3)).
Definition term262 := fun y0 : real => forall y1 : real -> Prop, (@FINITE real y1) -> (~ (y1 = (@EMPTY real))) -> (real_le y0 (inf y1)) -> (~ (forall y2 : real, (@IN real y2 y1) -> real_le y0 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> real_le y2 y4) -> (forall y2 : real, forall y3 : real, (real_le y2 y3) \/ (real_le y3 y2)) -> (forall y2 : real -> Prop, ((@FINITE real y2) /\ (~ (y2 = (@EMPTY real)))) -> (@IN real (inf y2) y2) /\ (forall y3 : real, (@IN real y3 y2) -> real_le (inf y2) y3)) -> False.
Definition term428 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((real_le x1 (inf x0)) /\ (real_le (inf x0) x2)) -> real_le x1 x2.
Definition term409 (x0 : real -> Prop) (x1 : real) := ((@FINITE real x0) /\ ((~ (x0 = (@EMPTY real))) /\ (@IN real x1 x0))) -> real_le (inf x0) x1.
Definition term36 (x0 : real) (x1 : real -> Prop) := @COND real (x1 = (@EMPTY real)) x0 (real_min x0 (inf x1)).
Definition term415 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ ((real_le x0 x2) \/ (~ (real_le x1 x2))).
Definition term60 (x0 : real -> Prop) (x1 : real) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> ((inf x0) = x1) = ((@IN real x1 x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)).
Definition term367 (x0 : real -> Prop) (x1 : real) := (~ (@FINITE real x0)) \/ ((x0 = (@EMPTY real)) \/ ((~ (@IN real x1 x0)) \/ (real_le (inf x0) x1))).
Definition term122 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => real_le (real_min x0 (inf x1)) y0) x2.
Definition term56 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@FINITE a0 (@INSERT a0 y0 x0)) = (@FINITE a0 x0).
Definition term93 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> (fun y1 : real => real_le x1 y1) y0.
Definition term202 (x0 : real -> Prop) (x1 : real) := real_le (inf x0) x1.
Definition term291 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term412 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x2)) \/ (real_le x1 x2).
Definition term69 (x0 : real) (x1 : real -> Prop) := @IN real x0 (@INSERT real x0 x1).
Definition term442 (x0 : real -> Prop) (x1 : real) := (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)) -> False.
Definition term281 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((@IN real x2 x0) -> real_le x1 x2).
Definition term78 (x0 : real) (x1 : real) := (fun y0 : real => real_le x0 y0) x1.
Definition term430 (x0 : real) (x1 : real) := (real_le x0 x1) -> False.
Definition term89 (x0 : real) := and (real_le x0 x0).
Definition term315 (x0 : real -> Prop) := (~ ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real))))) \/ ((@IN real (inf x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0)).
Definition term218 (x0 : real -> Prop) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN real x1 x0) = y0) -> (y0 -> (real_le (inf x0) x1) = y1) -> ((@IN real x1 x0) -> real_le (inf x0) x1) = (y0 -> y1)) x2.
Definition term184 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1)).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 (@INSERT a0 y0 y1)) -> x0 y2) = ((x0 y0) /\ (forall y2 : a0, (@IN a0 y2 y1) -> x0 y2)).
Definition term443 (x0 : real -> Prop) (x1 : real) := (~ (real_le x1 (inf x0))) -> (~ (real_le (inf x0) x1)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (inf y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1)).
Definition term359 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2)) x0.
Definition term173 (x0 : real -> Prop) (x1 : real) := (@IN real x1 (@INSERT real x1 x0)) /\ ((real_le x1 x1) /\ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)).
Definition term372 (x0 : real -> Prop) := (x0 = (@EMPTY real)) -> ~ (x0 = (@EMPTY real)).
Definition term448 (x0 : real) := fun y0 : real -> Prop => (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> (~ (real_le x0 (inf y0))) -> (~ (real_le (inf y0) x0)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> real_le y1 y3) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> ~ (forall y1 : real -> Prop, ((@FINITE real y1) /\ (~ (y1 = (@EMPTY real)))) -> (@IN real (inf y1) y1) /\ (forall y2 : real, (@IN real y2 y1) -> real_le (inf y1) y2)).
Definition term447 (x0 : real) := fun y0 : real -> Prop => (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> (~ (real_le x0 (inf y0))) -> (~ (real_le (inf y0) x0)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> real_le y1 y3) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> (forall y1 : real -> Prop, ((@FINITE real y1) /\ (~ (y1 = (@EMPTY real)))) -> (@IN real (inf y1) y1) /\ (forall y2 : real, (@IN real y2 y1) -> real_le (inf y1) y2)) -> False.
Definition term259 (x0 : real) := fun y0 : real -> Prop => (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> (real_le x0 (inf y0)) -> (~ (forall y1 : real, (@IN real y1 y0) -> real_le x0 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> real_le y1 y3) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> ~ (forall y1 : real -> Prop, ((@FINITE real y1) /\ (~ (y1 = (@EMPTY real)))) -> (@IN real (inf y1) y1) /\ (forall y2 : real, (@IN real y2 y1) -> real_le (inf y1) y2)).
Definition term258 (x0 : real) := fun y0 : real -> Prop => (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> (real_le x0 (inf y0)) -> (~ (forall y1 : real, (@IN real y1 y0) -> real_le x0 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> real_le y1 y3) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> (forall y1 : real -> Prop, ((@FINITE real y1) /\ (~ (y1 = (@EMPTY real)))) -> (@IN real (inf y1) y1) /\ (forall y2 : real, (@IN real y2 y1) -> real_le (inf y1) y2)) -> False.
Definition term416 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term459 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term456 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term182 (x0 : real) (x1 : real -> Prop) := ~ (real_le x0 (inf x1)).
Definition term249 (x0 : real -> Prop) (x1 : real) := imp (~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0)).
Definition term186 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0)).
Definition term373 (x0 : Prop) := x0 -> ~ x0.
Definition term462 (x0 : real) := (fun y0 : real => forall y1 : real -> Prop, (@FINITE real y1) -> (~ (y1 = (@EMPTY real))) -> (~ (real_le y0 (inf y1))) -> (~ (real_le (inf y1) y0)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> real_le y2 y4) -> (forall y2 : real, forall y3 : real, (real_le y2 y3) \/ (real_le y3 y2)) -> (forall y2 : real -> Prop, ((@FINITE real y2) /\ (~ (y2 = (@EMPTY real)))) -> (@IN real (inf y2) y2) /\ (forall y3 : real, (@IN real y3 y2) -> real_le (inf y2) y3)) -> False) x0.
Definition term432 (x0 : real) := (fun y0 : real => forall y1 : real -> Prop, (@FINITE real y1) -> (~ (y1 = (@EMPTY real))) -> (real_le y0 (inf y1)) -> (~ (forall y2 : real, (@IN real y2 y1) -> real_le y0 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> real_le y2 y4) -> (forall y2 : real, forall y3 : real, (real_le y2 y3) \/ (real_le y3 y2)) -> (forall y2 : real -> Prop, ((@FINITE real y2) /\ (~ (y2 = (@EMPTY real)))) -> (@IN real (inf y2) y2) /\ (forall y3 : real, (@IN real y3 y2) -> real_le (inf y2) y3)) -> False) x0.
Definition term40 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term299 (x0 : real) (x1 : real) := forall y0 : real, ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term292 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ (~ (real_le x1 x2)).
Definition term319 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (forall y0 : a0, x1 y0).
Definition term77 (x0 : real) := fun y0 : real => real_le x0 y0.
