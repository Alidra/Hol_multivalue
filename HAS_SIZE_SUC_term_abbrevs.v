Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term213 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := ~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2).
Definition term219 (a0 : Type') (x0 : a0) (x1 : nat) := fun y0 : a0 -> Prop => (x1 = (@CARD a0 (@DELETE a0 y0 x0))) -> (@CARD a0 (@DELETE a0 y0 x0)) = x1.
Definition term46 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq nat (@CARD a0 (@INSERT a0 x1 (@DELETE a0 x0 x1))).
Definition term296 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term246 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 -> Prop => ((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 x1 x2)))) -> (@CARD a0 x1) = (S x0)) (@INSERT a0 x2 (@DELETE a0 x1 x2)).
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop (@HAS_SIZE a0 x0 (S x1)).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0, (@IN a0 y0 x0) -> (@CARD a0 (@DELETE a0 x0 y0)) = x1.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0, (@IN a0 y0 x0) -> @HAS_SIZE a0 (@DELETE a0 x0 y0) x1.
Definition term43 (x0 : nat) := ~ ((NUMERAL 0) = (S x0)).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := ((@FINITE a0 (@DELETE a0 x0 x1)) -> (@CARD a0 (@INSERT a0 x1 (@DELETE a0 x0 x1))) = (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@CARD a0 (@DELETE a0 x0 x1)) (S (@CARD a0 (@DELETE a0 x0 x1))))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2.
Definition term200 := (~ False) -> False.
Definition term185 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) /\ (~ (x1 x2))) \/ (((~ (x2 = x0)) /\ ((~ (x1 x2)) \/ (x2 = x0))) /\ (x1 x2)).
Definition term322 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0 -> Prop) := ((@CARD a0 (@DELETE a0 x2 x1)) = x0) \/ (~ (@IN a0 x1 x2)).
Definition term129 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 x2 x0)))) -> (@CARD a0 (@DELETE a0 x2 x0)) = x1) x2.
Definition term57 (a0 : Type') (x0 : a0) := @eq nat (@CARD a0 (@DELETE a0 (@EMPTY a0) x0)).
Definition term304 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@FINITE a0 (@DELETE a0 y0 y1)) = (@FINITE a0 y0)) x0.
Definition term242 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((x1 = (@CARD a0 (@DELETE a0 y0 x0))) -> (@CARD a0 (@DELETE a0 y0 x0)) = x1)) -> False) x2.
Definition term317 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) /\ ((@CARD a0 x1) = (@CARD a0 x1)).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (@IN a0 x1 (@DELETE a0 x0 y0)) = ((@IN a0 x1 x0) /\ (~ (x1 = y0))).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = (S x1)).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : Prop => y0 \/ (~ y0)) (@FINITE a0 x0).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 (@DELETE a0 x0 x1)) = x2).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term263 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term50 := @eq nat (NUMERAL 0).
Definition term252 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := ~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2)).
Definition term99 (x0 : Prop) := ~ (~ x0).
Definition term328 (x0 : nat) (x1 : nat) := ((S x0) = (S x1)) \/ (~ (x0 = x1)).
Definition term234 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : nat => ~ ((@CARD a0 (@DELETE a0 x0 x1)) = y0)) (@CARD a0 (@DELETE a0 x0 x1)).
Definition term58 (a0 : Type') (x0 : a0) (x1 : nat) := (@FINITE a0 (@DELETE a0 (@EMPTY a0) x0)) /\ ((@CARD a0 (@DELETE a0 (@EMPTY a0) x0)) = x1).
Definition term339 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ ((@CARD a0 x0) = (S x1))) -> (@CARD a0 x0) = (S x1).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp ((@CARD a0 (@INSERT a0 x1 (@DELETE a0 x0 x1))) = (S (@CARD a0 (@DELETE a0 x0 x1)))).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x0 x1) /\ (~ (x1 = x2))).
Definition term262 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> ((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2).
Definition term193 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@DELETE a0 x0 y1)) = ((@IN a0 y0 x0) /\ (~ (y0 = y1)))) x1.
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and ((~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2))).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @COND nat False (@CARD a0 (@DELETE a0 x0 x1)).
Definition term139 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term309 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@FINITE a0 (@DELETE a0 x0 x1)) -> (@CARD a0 (@INSERT a0 x1 (@DELETE a0 x0 x1))) = (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@CARD a0 (@DELETE a0 x0 x1)) (S (@CARD a0 (@DELETE a0 x0 x1)))).
Definition term62 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term128 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 -> Prop => ((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 x1 x2)))) -> (@CARD a0 (@DELETE a0 x1 x2)) = x0) (@INSERT a0 x2 (@DELETE a0 x1 x2)).
Definition term281 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ~ ((@CARD a0 x0) = (S x1)).
Definition term187 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) \/ (~ (@FINITE a0 x0)).
Definition term138 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term342 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (~ (y0 = (@EMPTY a0))) -> (@FINITE a0 y0) -> (forall y2 : a0, (@IN a0 y2 y0) -> (@CARD a0 (@DELETE a0 y0 y2)) = x0) -> (@IN a0 y1 y0) -> (~ (((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 y0 y1)))) -> (@CARD a0 y0) = (S x0))) -> False) x1.
Definition term153 (x0 : Prop) := (~ x0) -> False.
Definition term149 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INSERT a0 x0 (@DELETE a0 x1 x0))) = (@IN a0 y0 x1).
Definition term314 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := True /\ (forall y0 : a0, (@IN a0 y0 x0) -> (@FINITE a0 (@DELETE a0 x0 y0)) /\ ((@CARD a0 (@DELETE a0 x0 y0)) = x1)).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @HAS_SIZE a0 x0 (S x1).
Definition term191 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term251 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False.
Definition term245 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => ((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, (fun y1 : a0 => ~ (@IN a0 y1 x0)) y0).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @IN a0 x1 (@DELETE a0 x0 x1).
Definition term160 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (~ ((x0 y0) -> forall y1 : a0, ((y1 = y0) \/ ((x0 y1) /\ (~ (y1 = y0)))) = (x0 y1))) -> False.
Definition term163 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> forall y1 : a0, ((y1 = y0) \/ ((x0 y1) /\ (~ (y1 = y0)))) = (x0 y1).
Definition term250 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @eq Prop (((@CARD a0 (@INSERT a0 x0 (@DELETE a0 x1 x0))) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2)).
Definition term319 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ ((S (@CARD a0 (@DELETE a0 x1 x0))) = (@CARD a0 x1))) -> (S (@CARD a0 (@DELETE a0 x1 x0))) = (@CARD a0 x1).
Definition term235 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((@CARD a0 (@DELETE a0 x0 x1)) = (@CARD a0 (@DELETE a0 x0 x1))).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @FINITE a0 (@DELETE a0 x0 x1).
Definition term206 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (@IN a0 x1 x0) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2.
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp ((@FINITE a0 (@DELETE a0 x0 x1)) -> (@CARD a0 (@INSERT a0 x1 (@DELETE a0 x0 x1))) = (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@CARD a0 (@DELETE a0 x0 x1)) (S (@CARD a0 (@DELETE a0 x0 x1))))).
Definition term61 (a0 : Type') := forall y0 : a0, True.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (@IN a0 x1 x0) -> @HAS_SIZE a0 (@DELETE a0 x0 x1) x2.
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := True -> (@CARD a0 (@INSERT a0 x1 (@DELETE a0 x0 x1))) = (S (@CARD a0 (@DELETE a0 x0 x1))).
Definition term7 (a0 : Type') := fun y0 : a0 -> Prop => (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0))).
Definition term340 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((@CARD a0 x0) = (S x1)) -> False.
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @COND nat False (@CARD a0 (@DELETE a0 x0 x1)) (S (@CARD a0 (@DELETE a0 x0 x1))).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x1 = x2)) /\ (~ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term303 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term312 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @CARD a0 (@INSERT a0 x1 (@DELETE a0 x0 x1)).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@CARD a0 (@DELETE a0 x0 x1)) (S (@CARD a0 (@DELETE a0 x0 x1))).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@FINITE a0 (@DELETE a0 x0 y0)) = (@FINITE a0 x0)) x1.
Definition term266 (a0 : Type') (x0 : a0 -> Prop) := imp (~ (x0 = (@EMPTY a0))).
Definition term183 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or (((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) /\ (~ (x1 x2))).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := @eq Prop ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term83 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term53 (a0 : Type') (x0 : a0) := and (@FINITE a0 (@DELETE a0 (@EMPTY a0) x0)).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (@FINITE a0 (@DELETE a0 x0 x1)).
Definition term265 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> ((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2).
Definition term198 (x0 : Prop) := (~ x0) -> x0.
Definition term280 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ ((@CARD a0 x0) = (S x1))) -> False.
Definition term313 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term338 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (((S (@CARD a0 (@DELETE a0 x1 x0))) = (@CARD a0 x1)) /\ ((S (@CARD a0 (@DELETE a0 x1 x0))) = (S x2))) -> (@CARD a0 x1) = (S x2).
Definition term106 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@DELETE a0 x1 x2).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => (@IN a0 y0 x0) -> (@FINITE a0 (@DELETE a0 x0 y0)) /\ ((@CARD a0 (@DELETE a0 x0 y0)) = x1).
Definition term285 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) := (fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ ((@CARD a0 (@DELETE a0 x0 y0)) = x1)) x2.
Definition term227 (a0 : Type') := fun y0 : nat => forall y1 : a0, forall y2 : a0 -> Prop, (y0 = (@CARD a0 (@DELETE a0 y2 y1))) -> (@CARD a0 (@DELETE a0 y2 y1)) = y0.
Definition term226 (a0 : Type') := fun y0 : nat => forall y1 : a0, forall y2 : a0 -> Prop, (~ ((y0 = (@CARD a0 (@DELETE a0 y2 y1))) -> (@CARD a0 (@DELETE a0 y2 y1)) = y0)) -> False.
Definition term240 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : a0 -> Prop, (~ ((y0 = (@CARD a0 (@DELETE a0 y2 y1))) -> (@CARD a0 (@DELETE a0 y2 y1)) = y0)) -> False) x0.
Definition term141 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 = x2) \/ (@IN a0 x0 (@DELETE a0 x1 x2)).
Definition term305 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term247 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 x2 x0)))) -> (@CARD a0 x2) = (S x1)) x2.
Definition term307 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term1 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1)))) x0.
Definition term257 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := ~ (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop ((@FINITE a0 x0) /\ ((@CARD a0 x0) = (S x1))).
Definition term301 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term335 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (~ ((S (@CARD a0 (@DELETE a0 x0 x1))) = (S x2))) -> (S (@CARD a0 (@DELETE a0 x0 x1))) = (S x2).
Definition term344 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (exists y0 : a0, @IN a0 y0 x0) -> (@CARD a0 x0) = (S x1).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) := @eq nat (@CARD a0 x0).
Definition term302 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term181 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0))))) /\ (x1 x2).
Definition term188 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term159 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))).
Definition term152 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0).
Definition term346 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((@CARD a0 x0) = (S x1)) -> forall y0 : a0, (@IN a0 y0 x0) -> (@CARD a0 (@DELETE a0 x0 y0)) = x1.
Definition term299 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term162 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (~ ((x0 y0) -> forall y1 : a0, ((y1 = y0) \/ ((x0 y1) /\ (~ (y1 = y0)))) = (x0 y1))) -> False.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, x0 y0).
Definition term182 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x2 = x0)) /\ ((~ (x1 x2)) \/ (x2 = x0))) /\ (x1 x2).
Definition term320 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((S (@CARD a0 (@DELETE a0 x1 x0))) = (@CARD a0 x1)).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := False /\ ((@CARD a0 (@DELETE a0 x0 x1)) = x2).
Definition term330 (x0 : nat) (x1 : nat) := @eq Prop (((S x0) = (S x1)) \/ (~ (x0 = x1))).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @eq Prop (((@CARD a0 (@INSERT a0 x1 (@DELETE a0 x0 x1))) = (S (@CARD a0 (@DELETE a0 x0 x1)))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2).
Definition term261 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False.
Definition term222 (a0 : Type') (x0 : nat) := fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((x0 = (@CARD a0 (@DELETE a0 y1 y0))) -> (@CARD a0 (@DELETE a0 y1 y0)) = x0)) -> False.
Definition term277 (a0 : Type') := fun y0 : nat => forall y1 : a0 -> Prop, forall y2 : a0, (~ (y1 = (@EMPTY a0))) -> (@FINITE a0 y1) -> (forall y3 : a0, (@IN a0 y3 y1) -> (@CARD a0 (@DELETE a0 y1 y3)) = y0) -> (@IN a0 y2 y1) -> ((@CARD a0 y1) = (S (@CARD a0 (@DELETE a0 y1 y2)))) -> (@CARD a0 y1) = (S y0).
Definition term276 (a0 : Type') := fun y0 : nat => forall y1 : a0 -> Prop, forall y2 : a0, (~ (y1 = (@EMPTY a0))) -> (@FINITE a0 y1) -> (forall y3 : a0, (@IN a0 y3 y1) -> (@CARD a0 (@DELETE a0 y1 y3)) = y0) -> (@IN a0 y2 y1) -> (~ (((@CARD a0 y1) = (S (@CARD a0 (@DELETE a0 y1 y2)))) -> (@CARD a0 y1) = (S y0))) -> False.
Definition term48 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term290 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ ((@CARD a0 x0) = (S (@CARD a0 (@DELETE a0 x0 x1))))) -> (@CARD a0 x0) = (S (@CARD a0 (@DELETE a0 x0 x1))).
Definition term248 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := ((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2).
Definition term337 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := ((S (@CARD a0 (@DELETE a0 x0 x1))) = (@CARD a0 x0)) /\ ((S (@CARD a0 (@DELETE a0 x0 x1))) = (S x2)).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, y0 y1)) = (exists y1 : a0, ~ (y0 y1))) x0.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (y0 = (@EMPTY a0))) = (exists y1 : a0, @IN a0 y1 y0)) x0.
Definition term289 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (~ (@IN a0 y0 x0)).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 x0)) x1.
Definition term166 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (~ ((y0 y1) -> forall y2 : a0, ((y2 = y1) \/ ((y0 y2) /\ (~ (y2 = y1)))) = (y0 y2))) -> False.
Definition term334 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := ((@CARD a0 (@DELETE a0 x0 x1)) = x2) -> (S (@CARD a0 (@DELETE a0 x0 x1))) = (S x2).
Definition term300 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term233 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (fun y0 : nat => ~ ((@CARD a0 (@DELETE a0 x0 x1)) = y0)) x2.
Definition term112 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term111 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term131 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((fun y0 : a0 -> Prop => ((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 x1 x2)))) -> (@CARD a0 (@DELETE a0 x1 x2)) = x0) (@INSERT a0 x2 (@DELETE a0 x1 x2))).
Definition term186 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) /\ (~ (x1 x2)).
Definition term147 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (@IN a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2))).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (@IN a0 x1 x0) -> (@FINITE a0 (@DELETE a0 x0 x1)) /\ ((@CARD a0 (@DELETE a0 x0 x1)) = x2).
Definition term256 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (((~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False) -> (~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False) -> ((~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False) -> (~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False.
Definition term347 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (((@CARD a0 x0) = (S x1)) -> forall y0 : a0, (@IN a0 y0 x0) -> (@CARD a0 (@DELETE a0 x0 y0)) = x1) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> (@CARD a0 (@DELETE a0 x0 y0)) = x1) -> (@CARD a0 x0) = (S x1)).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (~ (@IN a0 y0 x0)).
Definition term343 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) := (fun y0 : a0 => (~ (x0 = (@EMPTY a0))) -> (@FINITE a0 x0) -> (forall y1 : a0, (@IN a0 y1 x0) -> (@CARD a0 (@DELETE a0 x0 y1)) = x1) -> (@IN a0 y0 x0) -> (~ (((@CARD a0 x0) = (S (@CARD a0 (@DELETE a0 x0 y0)))) -> (@CARD a0 x0) = (S x1))) -> False) x2.
Definition term333 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) x0.
Definition term214 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := ((~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False) -> (~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False.
Definition term156 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term231 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := ~ ((@CARD a0 (@DELETE a0 x0 x1)) = x2).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => ~ (@IN a0 y0 x0)) x1).
Definition term168 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) = (x1 x2))) -> False.
Definition term273 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => forall y1 : a0, (~ (y0 = (@EMPTY a0))) -> (@FINITE a0 y0) -> (forall y2 : a0, (@IN a0 y2 y0) -> (@CARD a0 (@DELETE a0 y0 y2)) = x0) -> (@IN a0 y1 y0) -> ((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 y0 y1)))) -> (@CARD a0 y0) = (S x0).
Definition term272 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => forall y1 : a0, (~ (y0 = (@EMPTY a0))) -> (@FINITE a0 y0) -> (forall y2 : a0, (@IN a0 y2 y0) -> (@CARD a0 (@DELETE a0 y0 y2)) = x0) -> (@IN a0 y1 y0) -> (~ (((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 y0 y1)))) -> (@CARD a0 y0) = (S x0))) -> False.
Definition term2 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0))).
Definition term82 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> False.
Definition term284 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0, (~ (@IN a0 y0 x0)) \/ ((@CARD a0 (@DELETE a0 x0 y0)) = x1).
Definition term293 (a0 : Type') (x0 : a0 -> Prop) := ~ ((@CARD a0 x0) = (@CARD a0 x0)).
Definition term306 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term151 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) := and (~ (x0 = (@EMPTY a0))).
Definition term279 (a0 : Type') := forall y0 : nat, forall y1 : a0 -> Prop, forall y2 : a0, (~ (y1 = (@EMPTY a0))) -> (@FINITE a0 y1) -> (forall y3 : a0, (@IN a0 y3 y1) -> (@CARD a0 (@DELETE a0 y1 y3)) = y0) -> (@IN a0 y2 y1) -> ((@CARD a0 y1) = (S (@CARD a0 (@DELETE a0 y1 y2)))) -> (@CARD a0 y1) = (S y0).
Definition term278 (a0 : Type') := forall y0 : nat, forall y1 : a0 -> Prop, forall y2 : a0, (~ (y1 = (@EMPTY a0))) -> (@FINITE a0 y1) -> (forall y3 : a0, (@IN a0 y3 y1) -> (@CARD a0 (@DELETE a0 y1 y3)) = y0) -> (@IN a0 y2 y1) -> (~ (((@CARD a0 y1) = (S (@CARD a0 (@DELETE a0 y1 y2)))) -> (@CARD a0 y1) = (S y0))) -> False.
Definition term229 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : a0 -> Prop, (y0 = (@CARD a0 (@DELETE a0 y2 y1))) -> (@CARD a0 (@DELETE a0 y2 y1)) = y0.
Definition term228 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : a0 -> Prop, (~ ((y0 = (@CARD a0 (@DELETE a0 y2 y1))) -> (@CARD a0 (@DELETE a0 y2 y1)) = y0)) -> False.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (@EMPTY a0)).
Definition term60 (a0 : Type') := fun y0 : a0 => True.
Definition term175 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (x0 = x1)).
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ (~ (x1 = x2)).
Definition term254 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := ((~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False) -> (~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False.
Definition term195 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term190 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (@IN a0 x1 (@DELETE a0 x0 y0)) = ((@IN a0 x1 x0) /\ (~ (x1 = y0)))) x2.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@CARD a0 (@DELETE a0 x0 x1)).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ~ (@IN a0 y1 x0)) y0.
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> (@FINITE a0 (@DELETE a0 x0 y0)) /\ ((@CARD a0 (@DELETE a0 x0 y0)) = x1)).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := ~ (x0 = (@EMPTY a0)).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @INSERT a0 x1 (@DELETE a0 x0 x1).
Definition term255 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (((~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False) -> (~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False) -> (~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False.
Definition term86 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, ~ (@IN a0 y0 x0)).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term295 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term211 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2.
Definition term95 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (~ (@IN a0 x0 x1)).
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ (~ (x1 = x2)).
Definition term341 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, forall y2 : a0, (~ (y1 = (@EMPTY a0))) -> (@FINITE a0 y1) -> (forall y3 : a0, (@IN a0 y3 y1) -> (@CARD a0 (@DELETE a0 y1 y3)) = y0) -> (@IN a0 y2 y1) -> (~ (((@CARD a0 y1) = (S (@CARD a0 (@DELETE a0 y1 y2)))) -> (@CARD a0 y1) = (S y0))) -> False) x0.
Definition term161 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> forall y1 : a0, ((y1 = y0) \/ ((x0 y1) /\ (~ (y1 = y0)))) = (x0 y1).
Definition term136 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 (@DELETE a0 x1 x0))) = (@IN a0 y0 x1).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => @IN a0 y0 x0.
Definition term42 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term321 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> @IN a0 x0 x1.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x1 y0)) = (@COND nat (@IN a0 x1 y0) (@CARD a0 y0) (S (@CARD a0 y0)))) (@DELETE a0 x0 x1).
Definition term10 (a0 : Type') := forall y0 : a0 -> Prop, (~ (y0 = (@EMPTY a0))) = (exists y1 : a0, @IN a0 y1 y0).
Definition term135 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> (@INSERT a0 x0 (@DELETE a0 x1 x0)) = x1.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop ((@CARD a0 x0) = (S x1)).
Definition term260 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := imp (forall y0 : a0, (@IN a0 y0 x0) -> (@CARD a0 (@DELETE a0 x0 y0)) = x1).
Definition term271 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0, (~ (x0 = (@EMPTY a0))) -> (@FINITE a0 x0) -> (forall y1 : a0, (@IN a0 y1 x0) -> (@CARD a0 (@DELETE a0 x0 y1)) = x1) -> (@IN a0 y0 x0) -> ((@CARD a0 x0) = (S (@CARD a0 (@DELETE a0 x0 y0)))) -> (@CARD a0 x0) = (S x1).
Definition term270 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0, (~ (x0 = (@EMPTY a0))) -> (@FINITE a0 x0) -> (forall y1 : a0, (@IN a0 y1 x0) -> (@CARD a0 (@DELETE a0 x0 y1)) = x1) -> (@IN a0 y0 x0) -> (~ (((@CARD a0 x0) = (S (@CARD a0 (@DELETE a0 x0 y0)))) -> (@CARD a0 x0) = (S x1))) -> False.
Definition term298 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term237 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @eq Prop (~ ((@CARD a0 (@DELETE a0 x0 x1)) = x2)).
Definition term325 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (~ (~ (@IN a0 x1 x0))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2.
Definition term210 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0) := imp (x0 = (@CARD a0 (@DELETE a0 x1 x2))).
Definition term215 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (((~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False) -> (~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False) -> (~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False.
Definition term157 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False.
Definition term220 (a0 : Type') (x0 : a0) (x1 : nat) := forall y0 : a0 -> Prop, (~ ((x1 = (@CARD a0 (@DELETE a0 y0 x0))) -> (@CARD a0 (@DELETE a0 y0 x0)) = x1)) -> False.
Definition term259 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (@IN a0 x0 x1) -> ((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2).
Definition term221 (a0 : Type') (x0 : a0) (x1 : nat) := forall y0 : a0 -> Prop, (x1 = (@CARD a0 (@DELETE a0 y0 x0))) -> (@CARD a0 (@DELETE a0 y0 x0)) = x1.
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := ((@CARD a0 x0) = (S (@CARD a0 (@DELETE a0 x0 x1)))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2.
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (@FINITE a0 (@DELETE a0 x0 x1)) /\ ((@CARD a0 (@DELETE a0 x0 x1)) = x2).
Definition term196 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term292 (a0 : Type') (x0 : a0 -> Prop) := (~ ((@CARD a0 x0) = (@CARD a0 x0))) -> (@CARD a0 x0) = (@CARD a0 x0).
Definition term311 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term143 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term145 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term349 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 (S y1)) = ((~ (y0 = (@EMPTY a0))) /\ (forall y2 : a0, (@IN a0 y2 y0) -> @HAS_SIZE a0 (@DELETE a0 y0 y2) y1)).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> @HAS_SIZE a0 (@DELETE a0 x0 y0) x1).
Definition term236 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @eq Prop ((fun y0 : nat => ~ ((@CARD a0 (@DELETE a0 x0 x1)) = y0)) x2).
Definition term55 (a0 : Type') (x0 : a0) := @CARD a0 (@DELETE a0 (@EMPTY a0) x0).
Definition term224 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : a0 -> Prop, (~ ((x0 = (@CARD a0 (@DELETE a0 y1 y0))) -> (@CARD a0 (@DELETE a0 y1 y0)) = x0)) -> False.
Definition term241 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((x0 = (@CARD a0 (@DELETE a0 y1 y0))) -> (@CARD a0 (@DELETE a0 y1 y0)) = x0)) -> False) x1.
Definition term269 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => (~ (x0 = (@EMPTY a0))) -> (@FINITE a0 x0) -> (forall y1 : a0, (@IN a0 y1 x0) -> (@CARD a0 (@DELETE a0 x0 y1)) = x1) -> (@IN a0 y0 x0) -> ((@CARD a0 x0) = (S (@CARD a0 (@DELETE a0 x0 y0)))) -> (@CARD a0 x0) = (S x1).
Definition term268 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => (~ (x0 = (@EMPTY a0))) -> (@FINITE a0 x0) -> (forall y1 : a0, (@IN a0 y1 x0) -> (@CARD a0 (@DELETE a0 x0 y1)) = x1) -> (@IN a0 y0 x0) -> (~ (((@CARD a0 x0) = (S (@CARD a0 (@DELETE a0 x0 y0)))) -> (@CARD a0 x0) = (S x1))) -> False.
Definition term208 (x0 : nat) := @eq nat (S x0).
Definition term323 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @eq Prop ((~ (@IN a0 x1 x0)) \/ ((@CARD a0 (@DELETE a0 x0 x1)) = x2)).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := True /\ ((@CARD a0 (@DELETE a0 x0 x1)) = x2).
Definition term9 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0))).
Definition term150 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0).
Definition term267 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> ((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2).
Definition term253 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (~ (x1 = (@EMPTY a0))) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False.
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term243 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := ((@FINITE a0 (@DELETE a0 x1 x0)) -> (@CARD a0 (@INSERT a0 x0 (@DELETE a0 x1 x0))) = (@COND nat (@IN a0 x0 (@DELETE a0 x1 x0)) (@CARD a0 (@DELETE a0 x1 x0)) (S (@CARD a0 (@DELETE a0 x1 x0))))) -> (@CARD a0 x1) = (S x2).
Definition term205 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term258 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False.
Definition term88 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => ~ (@IN a0 y1 x0)) y0).
Definition term41 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (~ (forall y0 : a0, ~ (@IN a0 y0 x0))).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (~ (forall y0 : a0, (fun y1 : a0 => ~ (@IN a0 y1 x0)) y0)).
Definition term140 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)).
Definition term203 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (~ ((y0 y1) -> forall y2 : a0, ((y2 = y1) \/ ((y0 y2) /\ (~ (y2 = y1)))) = (y0 y2))) -> False) x0.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (@FINITE a0 (@DELETE a0 x0 x1)).
Definition term204 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (~ ((x0 y0) -> forall y1 : a0, ((y1 = y0) \/ ((x0 y1) /\ (~ (y1 = y0)))) = (x0 y1))) -> False) x1.
Definition term59 (a0 : Type') (x0 : a0) (x1 : nat) := False -> (@FINITE a0 (@DELETE a0 (@EMPTY a0) x0)) /\ ((@CARD a0 (@DELETE a0 (@EMPTY a0) x0)) = x1).
Definition term239 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((@CARD a0 (@DELETE a0 x0 x1)) = (@CARD a0 (@DELETE a0 x0 x1))) -> False.
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and (~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => (@IN a0 y0 x0) -> (@FINITE a0 x0) /\ ((@CARD a0 (@DELETE a0 x0 y0)) = x1).
Definition term283 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ ((@CARD a0 (@DELETE a0 x0 y0)) = x1).
Definition term238 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ ((@CARD a0 (@DELETE a0 x0 x1)) = (@CARD a0 (@DELETE a0 x0 x1)))) -> (@CARD a0 (@DELETE a0 x0 x1)) = (@CARD a0 (@DELETE a0 x0 x1)).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0, (@IN a0 y0 (@DELETE a0 x0 y1)) = ((@IN a0 y0 x0) /\ (~ (y0 = y1))).
Definition term336 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := ~ ((S (@CARD a0 (@DELETE a0 x0 x1))) = (S x2)).
Definition term201 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term308 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (@IN a0 x1 x0) -> (@FINITE a0 x0) /\ ((@CARD a0 (@DELETE a0 x0 x1)) = x2).
Definition term286 (x0 : nat) (x1 : nat) := (x0 = x1) -> (S x0) = (S x1).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => (@IN a0 y0 x0) -> @HAS_SIZE a0 (@DELETE a0 x0 y0) x1.
Definition term324 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0 -> Prop) := @eq Prop (((@CARD a0 (@DELETE a0 x2 x1)) = x0) \/ (~ (@IN a0 x1 x2))).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := False /\ ((@CARD a0 x0) = (S x1)).
Definition term44 (x0 : nat) := (~ ((NUMERAL 0) = (S x0))) -> ((NUMERAL 0) = (S x0)) = False.
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := ((@CARD a0 (@INSERT a0 x1 (@DELETE a0 x0 x1))) = (S (@CARD a0 (@DELETE a0 x0 x1)))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2.
Definition term84 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (@IN a0 y0 x0).
Definition term287 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term192 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term291 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((@CARD a0 x0) = (S (@CARD a0 (@DELETE a0 x0 x1)))).
Definition term199 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term230 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (~ ((@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False.
Definition term217 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := ~ (~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)).
Definition term331 (x0 : nat) (x1 : nat) := (~ (~ (x0 = x1))) -> (S x0) = (S x1).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (~ (~ (x1 = x2))).
Definition term164 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (~ ((y0 y1) -> forall y2 : a0, ((y2 = y1) \/ ((y0 y2) /\ (~ (y2 = y1)))) = (y0 y2))) -> False.
Definition term244 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := ((@CARD a0 (@INSERT a0 x0 (@DELETE a0 x1 x0))) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0, (@IN a0 y0 x0) -> (@FINITE a0 x0) /\ ((@CARD a0 (@DELETE a0 x0 y0)) = x1).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0, (@IN a0 y0 x0) -> (@FINITE a0 (@DELETE a0 x0 y0)) /\ ((@CARD a0 (@DELETE a0 x0 y0)) = x1).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @CARD a0 (@DELETE a0 x0 x1).
Definition term165 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (y0 y1) -> forall y2 : a0, ((y2 = y1) \/ ((y0 y2) /\ (~ (y2 = y1)))) = (y0 y2).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) := (~ (x0 = (@EMPTY a0))) -> (x0 = (@EMPTY a0)) = False.
Definition term47 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term223 (a0 : Type') (x0 : nat) := fun y0 : a0 => forall y1 : a0 -> Prop, (x0 = (@CARD a0 (@DELETE a0 y1 y0))) -> (@CARD a0 (@DELETE a0 y1 y0)) = x0.
Definition term184 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) /\ (~ (x1 x2))) \/ ((~ ((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0))))) /\ (x1 x2)).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq nat (@CARD a0 (@DELETE a0 x0 x1)).
Definition term315 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term209 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp ((@CARD a0 x0) = (S (@CARD a0 (@DELETE a0 x0 x1)))).
Definition term329 (x0 : nat) (x1 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((S x0) = (S x1))).
Definition term288 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) \/ ((S x0) = (S x1)).
Definition term212 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False.
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := S (@CARD a0 (@DELETE a0 x0 x1)).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (@IN a0 y0 x0).
Definition term101 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0, (@IN a0 y1 (@DELETE a0 y0 y2)) = ((@IN a0 y1 y0) /\ (~ (y1 = y2)))) x0.
Definition term216 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (((~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False) -> (~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False) -> ((~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False) -> (~ ((x2 = (@CARD a0 (@DELETE a0 x0 x1))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> False.
Definition term158 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> ((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False.
Definition term134 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 (@DELETE a0 x1 x0))) = (@IN a0 y0 x1).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @COND nat (@IN a0 x1 (@DELETE a0 x0 x1)).
Definition term218 (a0 : Type') (x0 : a0) (x1 : nat) := fun y0 : a0 -> Prop => (~ ((x1 = (@CARD a0 (@DELETE a0 y0 x0))) -> (@CARD a0 (@DELETE a0 y0 x0)) = x1)) -> False.
Definition term294 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term154 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0))) -> False.
Definition term282 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (~ (@IN a0 x1 x0)) \/ ((@CARD a0 (@DELETE a0 x0 x1)) = x2).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := fun y0 : a0 -> Prop => ((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 x0 x1)))) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2.
Definition term155 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ ((x1 y0) /\ (~ (y0 = x0)))) = (x1 y0)).
Definition term8 (a0 : Type') := fun y0 : a0 -> Prop => (~ (y0 = (@EMPTY a0))) = (exists y1 : a0, @IN a0 y1 y0).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ~ (@IN a0 y1 x0)) y0).
Definition term310 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@FINITE a0 (@DELETE a0 x0 y0)) = (@FINITE a0 x0).
Definition term318 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) /\ ((@CARD a0 x1) = (@CARD a0 x1))) -> (S (@CARD a0 (@DELETE a0 x1 x0))) = (@CARD a0 x1).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := (x0 = (@EMPTY a0)) \/ (~ (x0 = (@EMPTY a0))).
Definition term297 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term232 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : nat => ~ ((@CARD a0 (@DELETE a0 x0 x1)) = y0).
Definition term249 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((fun y0 : a0 -> Prop => ((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 x1 x2)))) -> (@CARD a0 x1) = (S x0)) (@INSERT a0 x2 (@DELETE a0 x1 x2))).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (x1 = x2).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) /\ (~ (x1 = x1)).
Definition term207 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, @IN a0 y0 x0.
Definition term327 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := (~ ((@CARD a0 (@DELETE a0 x0 x1)) = x2)) -> (@CARD a0 (@DELETE a0 x0 x1)) = x2.
Definition term225 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : a0 -> Prop, (x0 = (@CARD a0 (@DELETE a0 y1 y0))) -> (@CARD a0 (@DELETE a0 y1 y0)) = x0.
Definition term0 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1))).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term316 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term202 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term146 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))).
Definition term275 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, forall y1 : a0, (~ (y0 = (@EMPTY a0))) -> (@FINITE a0 y0) -> (forall y2 : a0, (@IN a0 y2 y0) -> (@CARD a0 (@DELETE a0 y0 y2)) = x0) -> (@IN a0 y1 y0) -> ((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 y0 y1)))) -> (@CARD a0 y0) = (S x0).
Definition term274 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, forall y1 : a0, (~ (y0 = (@EMPTY a0))) -> (@FINITE a0 y0) -> (forall y2 : a0, (@IN a0 y2 y0) -> (@CARD a0 (@DELETE a0 y0 y2)) = x0) -> (@IN a0 y1 y0) -> (~ (((@CARD a0 y0) = (S (@CARD a0 (@DELETE a0 y0 y1)))) -> (@CARD a0 y0) = (S x0))) -> False.
Definition term167 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (y0 y1) -> forall y2 : a0, ((y2 = y1) \/ ((y0 y2) /\ (~ (y2 = y1)))) = (y0 y2).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (fun y1 : a0 => ~ (@IN a0 y1 x0)) y0.
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2)).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @HAS_SIZE a0 (@DELETE a0 x0 x1) x2.
Definition term170 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term51 (a0 : Type') (x0 : a0) := @FINITE a0 (@DELETE a0 (@EMPTY a0) x0).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => (@IN a0 y0 x0) -> (@CARD a0 (@DELETE a0 x0 y0)) = x1.
Definition term169 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x2 = x0) \/ ((x1 x2) /\ (~ (x2 = x0)))) = (x1 x2)).
Definition term348 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 (S y0)) = ((~ (x0 = (@EMPTY a0))) /\ (forall y1 : a0, (@IN a0 y1 x0) -> @HAS_SIZE a0 (@DELETE a0 x0 y1) y0)).
Definition term345 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (forall y0 : a0, (@IN a0 y0 x0) -> (@CARD a0 (@DELETE a0 x0 y0)) = x1) -> (@CARD a0 x0) = (S x1).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := True /\ ((@CARD a0 x0) = (S x1)).
Definition term45 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term194 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x0.
Definition term264 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> (@CARD a0 (@DELETE a0 x1 y0)) = x2) -> (@IN a0 x0 x1) -> (~ (((@CARD a0 x1) = (S (@CARD a0 (@DELETE a0 x1 x0)))) -> (@CARD a0 x1) = (S x2))) -> False.
Definition term332 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
Definition term326 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (~ (~ (@IN a0 x0 x1))).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) -> (@FINITE a0 x0) = False.
