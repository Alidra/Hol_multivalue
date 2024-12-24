Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term220 (x0 : nat -> Prop) := (@FINITE nat x0) \/ (~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)).
Definition term421 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term267 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (@IN nat (x1 x2) x0) /\ (~ (Peano.le (x1 x2) x2)).
Definition term479 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) /\ (Peano.le x0 x1).
Definition term57 (x0 : nat -> Prop) := ~ (exists y0 : nat, ~ (@IN nat y0 x0)).
Definition term462 (x0 : nat) (x1 : nat -> Prop) := ~ ((~ (@FINITE nat x1)) \/ (~ (@IN nat x0 x1))).
Definition term401 (x0 : type992) (x1 : nat -> Prop) := forall y0 : nat, (@IN nat (x0 x1 y0) x1) /\ (~ (Peano.le (x0 x1 y0) y0)).
Definition term271 (x0 : nat -> Prop) (x1 : nat -> nat) := forall y0 : nat, (@IN nat (x1 y0) x0) /\ (~ (Peano.le (x1 y0) y0)).
Definition term466 (x0 : nat) (x1 : nat -> Prop) := (@FINITE nat x1) /\ (@IN nat x0 x1).
Definition term180 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0).
Definition term123 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term196 (x0 : nat -> Prop) := ~ (all x0).
Definition term68 (x0 : type993) := ~ (all x0).
Definition term482 := (~ False) -> False.
Definition term136 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) /\ (~ (Peano.lt x0 x1)).
Definition term396 (x0 : nat) (x1 : type994) (x2 : nat -> Prop) := (~ (@IN nat x0 x2)) \/ (Peano.le x0 (x1 x2)).
Definition term402 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term95 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term37 := fun y0 : nat -> Prop => (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1).
Definition term73 := fun y0 : nat -> Prop => ~ ((fun y1 : nat -> Prop => (@FINITE nat y1) -> exists y2 : nat, ~ (@IN nat y2 y1)) y0).
Definition term62 (x0 : nat -> Prop) := fun y0 : nat => @IN nat y0 x0.
Definition term172 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0).
Definition term150 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0).
Definition term115 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term92 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term215 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0).
Definition term35 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0.
Definition term352 (x0 : type994) := fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (forall y1 : nat, (~ (@IN nat y1 y0)) \/ (Peano.le y1 (x0 y0))).
Definition term356 := fun y0 : type994 => forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1))).
Definition term395 := exists y0 : type992, exists y1 : type994, (forall y2 : nat -> Prop, (@FINITE nat y2) \/ (forall y3 : nat, (@IN nat (y0 y2 y3) y2) /\ (~ (Peano.le (y0 y2 y3) y3)))) /\ (forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))).
Definition term433 (x0 : type994) (x1 : nat -> Prop) := ~ ((x0 x1) = (x0 x1)).
Definition term32 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (@IN nat y0 x0) -> Peano.le y0 x1.
Definition term437 (x0 : Prop) := ~ (~ x0).
Definition term348 (x0 : type994) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => fun y1 : nat => (~ (@FINITE nat y0)) \/ (forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1))) x1 (x0 x1).
Definition term465 (x0 : nat -> Prop) := and (~ (~ (@FINITE nat x0))).
Definition term280 (x0 : nat -> Prop) := (@FINITE nat x0) \/ (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0).
Definition term453 (x0 : type994) (x1 : nat) (x2 : nat -> Prop) := (~ (@FINITE nat x2)) \/ ((Peano.le x1 (x0 x2)) \/ (~ (@IN nat x1 x2))).
Definition term70 := exists y0 : nat -> Prop, ~ ((fun y1 : nat -> Prop => (@FINITE nat y1) -> exists y2 : nat, ~ (@IN nat y2 y1)) y0).
Definition term61 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => ~ (@IN nat y1 x0)) y0).
Definition term265 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))) x2 (x1 x2).
Definition term317 := and (exists y0 : type992, forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (y0 y1 y2) y1) /\ (~ (Peano.le (y0 y1 y2) y2)))).
Definition term254 (x0 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (@IN nat y3 x0) /\ (~ (Peano.le y3 y2))) y0 y1.
Definition term252 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term213 (x0 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0)).
Definition term158 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0).
Definition term101 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term140 (x0 : nat) (x1 : nat) := (Peano.lt x0 (S x1)) \/ ((~ (x0 = x1)) /\ (~ (Peano.lt x0 x1))).
Definition term344 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat -> Prop => fun y2 : nat => (~ (@FINITE nat y1)) \/ (forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2))) x0 y0.
Definition term30 := (~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> ~ (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)).
Definition term233 := fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1)).
Definition term22 := ~ (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)).
Definition term3 := ~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)).
Definition term458 (x0 : nat) (x1 : type994) (x2 : nat -> Prop) := (~ ((~ (@FINITE nat x2)) \/ (~ (@IN nat x0 x2)))) -> Peano.le x0 (x1 x2).
Definition term308 (x0 : type992) (x1 : nat -> Prop) := (fun y0 : nat -> nat => (@FINITE nat x1) \/ (forall y1 : nat, (@IN nat (y0 y1) x1) /\ (~ (Peano.le (y0 y1) y1)))) (x0 x1).
Definition term451 (x0 : type994) (x1 : nat) (x2 : nat -> Prop) := (Peano.le x1 (x0 x2)) \/ (~ (@IN nat x1 x2)).
Definition term403 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term320 (x0 : nat -> Prop) := (~ (@FINITE nat x0)) \/ (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0).
Definition term397 (x0 : type994) (x1 : nat -> Prop) := fun y0 : nat => (~ (@IN nat y0 x1)) \/ (Peano.le y0 (x0 x1)).
Definition term14 := and (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False).
Definition term445 (x0 : type994) (x1 : nat -> Prop) := ~ (Peano.lt (x0 x1) (S (x0 x1))).
Definition term394 := fun y0 : type992 => exists y1 : type994, (forall y2 : nat -> Prop, (@FINITE nat y2) \/ (forall y3 : nat, (@IN nat (y0 y2 y3) y2) /\ (~ (Peano.le (y0 y2 y3) y3)))) /\ (forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))).
Definition term379 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term173 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0).
Definition term151 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0).
Definition term116 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term93 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term191 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term134 := (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term85 (x0 : nat) := forall y0 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term467 (x0 : nat) (x1 : nat -> Prop) := imp (~ ((~ (@FINITE nat x1)) \/ (~ (@IN nat x0 x1)))).
Definition term342 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ (@FINITE nat x0)) \/ (forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0))) x1.
Definition term210 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0) x1).
Definition term286 (x0 : nat -> Prop) := @eq Prop ((@FINITE nat x0) \/ (exists y0 : nat -> nat, forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1)))).
Definition term285 (x0 : nat -> Prop) := @eq Prop ((@FINITE nat x0) \/ (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0)).
Definition term204 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (@IN nat y0 x0) /\ (~ (Peano.le y0 x1)).
Definition term221 (x0 : nat -> Prop) := (@FINITE nat x0) \/ (forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))).
Definition term153 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term349 (x0 : type994) (x1 : nat -> Prop) := (fun y0 : nat => (~ (@FINITE nat x1)) \/ (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0))) (x0 x1).
Definition term333 := fun y0 : nat -> Prop => exists y1 : nat, (~ (@FINITE nat y0)) \/ (forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1)).
Definition term373 (x0 : type992) := ((fun y0 : type992 => forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (y0 y1 y2) y1) /\ (~ (Peano.le (y0 y1 y2) y2)))) x0) /\ (exists y0 : type994, forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1)))).
Definition term83 (x0 : nat) (x1 : nat) := ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))) /\ ((Peano.lt x1 x0) \/ (Peano.le x0 x1)).
Definition term408 (x0 : type994) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (@IN nat y0 x1)) \/ (Peano.le y0 (x0 x1))) x2.
Definition term287 (x0 : nat -> Prop) (x1 : nat -> nat) := (@FINITE nat x0) \/ ((fun y0 : nat -> nat => forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))) x1).
Definition term390 (x0 : type992) (x1 : type994) := (forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, (@IN nat (x0 y0 y1) y0) /\ (~ (Peano.le (x0 y0 y1) y1)))) /\ (forall y0 : nat -> Prop, (~ (@FINITE nat y0)) \/ (forall y1 : nat, (~ (@IN nat y1 y0)) \/ (Peano.le y1 (x1 y0)))).
Definition term249 := (forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, exists y2 : nat, (@IN nat y2 y0) /\ (~ (Peano.le y2 y1)))) /\ (forall y0 : nat -> Prop, (~ (@FINITE nat y0)) \/ (exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1))).
Definition term410 (x0 : type994) (x1 : nat -> Prop) := forall y0 : nat, (fun y1 : nat => (~ (@IN nat y1 x1)) \/ (Peano.le y1 (x0 x1))) y0.
Definition term167 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0.
Definition term162 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0.
Definition term110 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0.
Definition term105 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0.
Definition term389 (x0 : type992) (x1 : type994) := (forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, (@IN nat (x0 y0 y1) y0) /\ (~ (Peano.le (x0 y0 y1) y1)))) /\ ((fun y0 : type994 => forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1)))) x1).
Definition term380 (x0 : Prop) (x1 : type252) := x0 /\ (exists y0 : type994, x1 y0).
Definition term60 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => ~ (@IN nat y0 x0)) x1).
Definition term319 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term258 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))) x1 x2.
Definition term422 (x0 : nat) := fun y0 : nat => ((Peano.lt x0 (S y0)) \/ (~ (x0 = y0))) /\ ((Peano.lt x0 (S y0)) \/ (~ (Peano.lt x0 y0))).
Definition term351 (x0 : type994) := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => fun y2 : nat => (~ (@FINITE nat y1)) \/ (forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2))) y0 (x0 y0).
Definition term310 (x0 : type992) := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => fun y2 : nat -> nat => (@FINITE nat y1) \/ (forall y3 : nat, (@IN nat (y2 y3) y1) /\ (~ (Peano.le (y2 y3) y3)))) y0 (x0 y0).
Definition term448 (x0 : type994) (x1 : nat -> Prop) := S (x0 x1).
Definition term99 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term222 (x0 : nat -> Prop) := and ((@FINITE nat x0) \/ (~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0))).
Definition term330 (x0 : nat -> Prop) := fun y0 : nat => (~ (@FINITE nat x0)) \/ ((fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0).
Definition term435 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term90 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term269 (x0 : nat -> Prop) (x1 : nat -> nat) := fun y0 : nat => (@IN nat (x1 y0) x0) /\ (~ (Peano.le (x1 y0) y0)).
Definition term393 (x0 : type992) := exists y0 : type994, (forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (x0 y1 y2) y1) /\ (~ (Peano.le (x0 y1 y2) y2)))) /\ (forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1)))).
Definition term198 (x0 : nat -> Prop) (x1 : nat) := ~ (forall y0 : nat, (@IN nat y0 x0) -> Peano.le y0 x1).
Definition term218 (x0 : nat -> Prop) := (~ (@FINITE nat x0)) \/ (exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)).
Definition term217 (x0 : nat -> Prop) := (~ (@FINITE nat x0)) \/ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0).
Definition term170 := fun y0 : nat => (forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term113 := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term406 (x0 : type994) (x1 : nat -> Prop) := (~ (@FINITE nat x1)) \/ (forall y0 : nat, (fun y1 : nat => (~ (@IN nat y1 x1)) \/ (Peano.le y1 (x0 x1))) y0).
Definition term240 := @eq Prop (forall y0 : nat -> Prop, ((@FINITE nat y0) \/ (forall y1 : nat, exists y2 : nat, (@IN nat y2 y0) /\ (~ (Peano.le y2 y1)))) /\ ((~ (@FINITE nat y0)) \/ (exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1)))).
Definition term50 (x0 : nat -> Prop) := exists y0 : nat, ~ (@IN nat y0 x0).
Definition term304 := fun y0 : nat -> Prop => exists y1 : nat -> nat, (fun y2 : nat -> Prop => fun y3 : nat -> nat => (@FINITE nat y2) \/ (forall y4 : nat, (@IN nat (y3 y4) y2) /\ (~ (Peano.le (y3 y4) y4)))) y0 y1.
Definition term378 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term474 (x0 : type994) (x1 : nat -> Prop) := ~ (Peano.le (S (x0 x1)) (x0 x1)).
Definition term443 (x0 : type994) (x1 : nat -> Prop) := Peano.lt (x0 x1) (S (x0 x1)).
Definition term15 := and (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))).
Definition term475 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term223 (x0 : nat -> Prop) := and ((@FINITE nat x0) \/ (forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0)))).
Definition term434 (x0 : Prop) := (~ x0) -> x0.
Definition term375 := fun y0 : type992 => ((fun y1 : type992 => forall y2 : nat -> Prop, (@FINITE nat y2) \/ (forall y3 : nat, (@IN nat (y1 y2 y3) y2) /\ (~ (Peano.le (y1 y2 y3) y3)))) y0) /\ (exists y1 : type994, forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))).
Definition term413 (x0 : type994) (x1 : nat -> Prop) (x2 : nat) := (~ (@FINITE nat x1)) \/ ((fun y0 : nat => (~ (@IN nat y0 x1)) \/ (Peano.le y0 (x0 x1))) x2).
Definition term279 (x0 : Prop) (x1 : type1002) := exists y0 : nat -> nat, x0 \/ (x1 y0).
Definition term391 (x0 : type992) := fun y0 : type994 => (forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (x0 y1 y2) y1) /\ (~ (Peano.le (x0 y1 y2) y2)))) /\ ((fun y1 : type994 => forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))) y0).
Definition term24 := ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False.
Definition term256 (x0 : nat -> Prop) := fun y0 : nat => fun y1 : nat => (@IN nat y1 x0) /\ (~ (Peano.le y1 y0)).
Definition term12 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term226 := fun y0 : nat -> Prop => ((@FINITE nat y0) \/ (forall y1 : nat, exists y2 : nat, (@IN nat y2 y0) /\ (~ (Peano.le y2 y1)))) /\ ((~ (@FINITE nat y0)) \/ (exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1))).
Definition term328 (x0 : nat -> Prop) (x1 : nat) := (~ (@FINITE nat x0)) \/ ((fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) x1).
Definition term40 (x0 : nat) := fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term461 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term212 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0)).
Definition term307 (x0 : type992) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => fun y1 : nat -> nat => (@FINITE nat y0) \/ (forall y2 : nat, (@IN nat (y1 y2) y0) /\ (~ (Peano.le (y1 y2) y2)))) x1 (x0 x1).
Definition term250 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term234 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (@FINITE nat y0) \/ (forall y1 : nat, exists y2 : nat, (@IN nat y2 y0) /\ (~ (Peano.le y2 y1)))) x0.
Definition term374 (x0 : type992) := (forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, (@IN nat (x0 y0 y1) y0) /\ (~ (Peano.le (x0 y0 y1) y1)))) /\ (exists y0 : type994, forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1)))).
Definition term314 := fun y0 : type992 => forall y1 : nat -> Prop, (fun y2 : nat -> Prop => fun y3 : nat -> nat => (@FINITE nat y2) \/ (forall y4 : nat, (@IN nat (y3 y4) y2) /\ (~ (Peano.le (y3 y4) y4)))) y1 (y0 y1).
Definition term94 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0)).
Definition term84 (x0 : nat) := fun y0 : nat => ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term268 (x0 : nat -> Prop) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (@IN nat y2 x0) /\ (~ (Peano.le y2 y1))) y0 (x1 y0).
Definition term476 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term182 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term181 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0)).
Definition term160 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ ((~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0)))).
Definition term159 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0)).
Definition term125 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0))).
Definition term124 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0)).
Definition term103 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0))).
Definition term102 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0)).
Definition term357 := exists y0 : type994, forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1))).
Definition term338 := exists y0 : type994, forall y1 : nat -> Prop, (fun y2 : nat -> Prop => fun y3 : nat => (~ (@FINITE nat y2)) \/ (forall y4 : nat, (~ (@IN nat y4 y2)) \/ (Peano.le y4 y3))) y1 (y0 y1).
Definition term336 (x0 : type991) := exists y0 : type994, forall y1 : nat -> Prop, x0 y1 (y0 y1).
Definition term316 := exists y0 : type992, forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (y0 y1 y2) y1) /\ (~ (Peano.le (y0 y1 y2) y2))).
Definition term297 := exists y0 : type992, forall y1 : nat -> Prop, (fun y2 : nat -> Prop => fun y3 : nat -> nat => (@FINITE nat y2) \/ (forall y4 : nat, (@IN nat (y3 y4) y2) /\ (~ (Peano.le (y3 y4) y4)))) y1 (y0 y1).
Definition term295 (x0 : type986) := exists y0 : type992, forall y1 : nat -> Prop, x0 y1 (y0 y1).
Definition term274 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1)).
Definition term255 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (@IN nat y3 x0) /\ (~ (Peano.le y3 y2))) y1 (y0 y1).
Definition term253 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term463 (x0 : nat) (x1 : nat -> Prop) := (~ (~ (@FINITE nat x1))) /\ (~ (~ (@IN nat x0 x1))).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term332 (x0 : nat -> Prop) := exists y0 : nat, (~ (@FINITE nat x0)) \/ (forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)).
Definition term17 := (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term472 (x0 : type994) (x1 : nat -> Prop) := Peano.le (S (x0 x1)) (x0 x1).
Definition term257 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))) x1.
Definition term404 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (forall y0 : nat, x1 y0).
Definition term192 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term377 := exists y0 : type992, (forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (y0 y1 y2) y1) /\ (~ (Peano.le (y0 y1 y2) y2)))) /\ (exists y1 : type994, forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))).
Definition term454 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term323 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) x1.
Definition term209 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0) x1.
Definition term447 (x0 : type994) (x1 : nat -> Prop) := @IN nat (S (x0 x1)) x1.
Definition term141 (x0 : nat) (x1 : nat) := and ((Peano.lt x0 (S x1)) \/ (~ ((x0 = x1) \/ (Peano.lt x0 x1)))).
Definition term381 (x0 : Prop) (x1 : type252) := exists y0 : type994, x0 /\ (x1 y0).
Definition term214 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0).
Definition term118 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term46 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term34 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0.
Definition term340 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => fun y1 : nat => (~ (@FINITE nat y0)) \/ (forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1))) x0.
Definition term76 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term469 (x0 : nat) (x1 : type994) (x2 : nat -> Prop) := ((@FINITE nat x2) /\ (@IN nat x0 x2)) -> Peano.le x0 (x1 x2).
Definition term39 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term358 := (exists y0 : type992, forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (y0 y1 y2) y1) /\ (~ (Peano.le (y0 y1 y2) y2)))) /\ (exists y0 : type994, forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1)))).
Definition term427 (x0 : type994) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, (~ (@FINITE nat y0)) \/ ((~ (@IN nat y1 y0)) \/ (Peano.le y1 (x0 y0)))) x1.
Definition term282 (x0 : nat -> Prop) (x1 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))) x1.
Definition term412 (x0 : type994) (x1 : nat -> Prop) := @eq Prop ((~ (@FINITE nat x1)) \/ (forall y0 : nat, (~ (@IN nat y0 x1)) \/ (Peano.le y0 (x0 x1)))).
Definition term411 (x0 : type994) (x1 : nat -> Prop) := @eq Prop ((~ (@FINITE nat x1)) \/ (forall y0 : nat, (fun y1 : nat => (~ (@IN nat y1 x1)) \/ (Peano.le y1 (x0 x1))) y0)).
Definition term111 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term248 := forall y0 : nat -> Prop, (~ (@FINITE nat y0)) \/ (exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1)).
Definition term281 (x0 : nat -> Prop) := exists y0 : nat -> nat, (@FINITE nat x0) \/ ((fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0).
Definition term278 (x0 : Prop) (x1 : type1002) := x0 \/ (exists y0 : nat -> nat, x1 y0).
Definition term11 := fun y0 : nat => ~ (Peano.lt y0 (NUMERAL 0)).
Definition term97 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1)).
Definition term428 (x0 : type994) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (@FINITE nat x1)) \/ ((~ (@IN nat y0 x1)) \/ (Peano.le y0 (x0 x1)))) x2.
Definition term322 (x0 : nat -> Prop) := ~ (@FINITE nat x0).
Definition term237 (x0 : nat -> Prop) := ((fun y0 : nat -> Prop => (@FINITE nat y0) \/ (forall y1 : nat, exists y2 : nat, (@IN nat y2 y0) /\ (~ (Peano.le y2 y1)))) x0) /\ ((fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1))) x0).
Definition term13 := forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0)).
Definition term471 (x0 : type994) (x1 : nat -> Prop) := ((@FINITE nat x1) /\ (@IN nat (S (x0 x1)) x1)) -> Peano.le (S (x0 x1)) (x0 x1).
Definition term260 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (@IN nat y2 x0) /\ (~ (Peano.le y2 y1))) x1 y0.
Definition term420 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (S x1)) \/ (~ (x0 = x1))) /\ ((Peano.lt x0 (S x1)) \/ (~ (Peano.lt x0 x1))).
Definition term431 (x0 : nat) (x1 : nat) := (Peano.lt x0 (S x1)) \/ (~ (x0 = x1)).
Definition term104 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0.
Definition term450 (x0 : type994) (x1 : nat -> Prop) := ~ (@IN nat (S (x0 x1)) x1).
Definition term78 (x0 : nat) (x1 : nat) := or (Peano.lt x0 x1).
Definition term49 (x0 : nat -> Prop) := fun y0 : nat => ~ (@IN nat y0 x0).
Definition term370 := @eq Prop ((exists y0 : type992, forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (y0 y1 y2) y1) /\ (~ (Peano.le (y0 y1 y2) y2)))) /\ (exists y0 : type994, forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1))))).
Definition term369 := @eq Prop ((exists y0 : type992, (fun y1 : type992 => forall y2 : nat -> Prop, (@FINITE nat y2) \/ (forall y3 : nat, (@IN nat (y1 y2 y3) y2) /\ (~ (Peano.le (y1 y2 y3) y3)))) y0) /\ (exists y0 : type994, forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1))))).
Definition term74 := fun y0 : nat -> Prop => (@FINITE nat y0) /\ (forall y1 : nat, @IN nat y1 y0).
Definition term31 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x1 x0) -> Peano.le x1 x2.
Definition term289 (x0 : nat -> Prop) := fun y0 : nat -> nat => (@FINITE nat x0) \/ ((fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0).
Definition term449 (x0 : type994) (x1 : nat -> Prop) := (~ (@IN nat (S (x0 x1)) x1)) -> @IN nat (S (x0 x1)) x1.
Definition term418 (x0 : type994) := fun y0 : nat -> Prop => forall y1 : nat, (~ (@FINITE nat y0)) \/ ((~ (@IN nat y1 y0)) \/ (Peano.le y1 (x0 y0))).
Definition term273 (x0 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1)).
Definition term272 (x0 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (@IN nat y3 x0) /\ (~ (Peano.le y3 y2))) y1 (y0 y1).
Definition term386 := exists y0 : type994, (fun y1 : type994 => forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))) y0.
Definition term367 := exists y0 : type992, (fun y1 : type992 => forall y2 : nat -> Prop, (@FINITE nat y2) \/ (forall y3 : nat, (@IN nat (y1 y2 y3) y2) /\ (~ (Peano.le (y1 y2 y3) y3)))) y0.
Definition term284 (x0 : nat -> Prop) := exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0.
Definition term206 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1).
Definition term44 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term337 := forall y0 : nat -> Prop, exists y1 : nat, (fun y2 : nat -> Prop => fun y3 : nat => (~ (@FINITE nat y2)) \/ (forall y4 : nat, (~ (@IN nat y4 y2)) \/ (Peano.le y4 y3))) y0 y1.
Definition term335 (x0 : type991) := forall y0 : nat -> Prop, exists y1 : nat, x0 y0 y1.
Definition term296 := forall y0 : nat -> Prop, exists y1 : nat -> nat, (fun y2 : nat -> Prop => fun y3 : nat -> nat => (@FINITE nat y2) \/ (forall y4 : nat, (@IN nat (y3 y4) y2) /\ (~ (Peano.le (y3 y4) y4)))) y0 y1.
Definition term294 (x0 : type986) := forall y0 : nat -> Prop, exists y1 : nat -> nat, x0 y0 y1.
Definition term264 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))).
Definition term263 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (@IN nat y3 x0) /\ (~ (Peano.le y3 y2))) y0 y1).
Definition term7 := (((~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False) -> (~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False) -> ((~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False) -> (~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False.
Definition term355 := fun y0 : type994 => forall y1 : nat -> Prop, (fun y2 : nat -> Prop => fun y3 : nat => (~ (@FINITE nat y2)) \/ (forall y4 : nat, (~ (@IN nat y4 y2)) \/ (Peano.le y4 y3))) y1 (y0 y1).
Definition term165 (x0 : nat) := and (forall y0 : nat, (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))).
Definition term108 (x0 : nat) := and (forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))).
Definition term1 := forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0).
Definition term228 (x0 : type993) (x1 : type993) := forall y0 : nat -> Prop, (x0 y0) /\ (x1 y0).
Definition term9 (x0 : nat) := ~ (Peano.lt x0 (NUMERAL 0)).
Definition term309 (x0 : type992) (x1 : nat -> Prop) := (@FINITE nat x1) \/ (forall y0 : nat, (@IN nat (x0 x1 y0) x1) /\ (~ (Peano.le (x0 x1 y0) y0))).
Definition term5 := ((~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False) -> (~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False.
Definition term48 (x0 : nat) (x1 : nat -> Prop) := ~ (@IN nat x0 x1).
Definition term327 (x0 : nat -> Prop) := @eq Prop ((~ (@FINITE nat x0)) \/ (exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0))).
Definition term326 (x0 : nat -> Prop) := @eq Prop ((~ (@FINITE nat x0)) \/ (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0)).
Definition term23 := forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1).
Definition term440 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term347 := @eq Prop (forall y0 : nat -> Prop, exists y1 : nat, (~ (@FINITE nat y0)) \/ (forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1))).
Definition term346 := @eq Prop (forall y0 : nat -> Prop, exists y1 : nat, (fun y2 : nat -> Prop => fun y3 : nat => (~ (@FINITE nat y2)) \/ (forall y4 : nat, (~ (@IN nat y4 y2)) \/ (Peano.le y4 y3))) y0 y1).
Definition term306 := @eq Prop (forall y0 : nat -> Prop, exists y1 : nat -> nat, (@FINITE nat y0) \/ (forall y2 : nat, (@IN nat (y1 y2) y0) /\ (~ (Peano.le (y1 y2) y2)))).
Definition term305 := @eq Prop (forall y0 : nat -> Prop, exists y1 : nat -> nat, (fun y2 : nat -> Prop => fun y3 : nat -> nat => (@FINITE nat y2) \/ (forall y4 : nat, (@IN nat (y3 y4) y2) /\ (~ (Peano.le (y3 y4) y4)))) y0 y1).
Definition term339 := fun y0 : nat -> Prop => fun y1 : nat => (~ (@FINITE nat y0)) \/ (forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1)).
Definition term152 (x0 : nat) := fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0))).
Definition term459 (x0 : nat) (x1 : nat -> Prop) := (~ (@FINITE nat x1)) \/ (~ (@IN nat x0 x1)).
Definition term154 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) x1.
Definition term457 (x0 : type994) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((Peano.le x1 (x0 x2)) \/ ((~ (@FINITE nat x2)) \/ (~ (@IN nat x1 x2)))).
Definition term20 := imp ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term19 := imp ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term236 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1))) x0.
Definition term277 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term283 (x0 : nat -> Prop) := fun y0 : nat -> nat => (fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0.
Definition term142 (x0 : nat) (x1 : nat) := and ((Peano.lt x0 (S x1)) \/ ((~ (x0 = x1)) /\ (~ (Peano.lt x0 x1)))).
Definition term33 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (@IN nat y0 x0) -> Peano.le y0 x1.
Definition term53 := fun y0 : nat -> Prop => (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0).
Definition term399 (x0 : type992) (x1 : nat -> Prop) (x2 : nat) := (@IN nat (x0 x1 x2) x1) /\ (~ (Peano.le (x0 x1 x2) x2)).
Definition term247 := forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (exists y2 : nat, forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2))) y0.
Definition term242 := forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (@FINITE nat y1) \/ (forall y2 : nat, exists y3 : nat, (@IN nat y3 y1) /\ (~ (Peano.le y3 y2)))) y0.
Definition term409 (x0 : type994) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (~ (@IN nat y1 x1)) \/ (Peano.le y1 (x0 x1))) y0.
Definition term166 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0.
Definition term161 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0.
Definition term478 (x0 : nat) (x1 : nat) := ((Peano.lt x1 x0) /\ (Peano.le x0 x1)) -> False.
Definition term259 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 x0) /\ (~ (Peano.le y0 x1))) x2.
Definition term417 (x0 : type994) (x1 : nat -> Prop) := forall y0 : nat, (~ (@FINITE nat x1)) \/ ((~ (@IN nat y0 x1)) \/ (Peano.le y0 (x0 x1))).
Definition term460 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term27 := (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False.
Definition term456 (x0 : nat) (x1 : type994) (x2 : nat -> Prop) := @eq Prop ((~ (@FINITE nat x2)) \/ ((~ (@IN nat x0 x2)) \/ (Peano.le x0 (x1 x2)))).
Definition term382 (x0 : type992) := (forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, (@IN nat (x0 y0 y1) y0) /\ (~ (Peano.le (x0 y0 y1) y1)))) /\ (exists y0 : type994, (fun y1 : type994 => forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))) y0).
Definition term425 := forall y0 : nat, forall y1 : nat, ((Peano.lt y0 (S y1)) \/ (~ (y0 = y1))) /\ ((Peano.lt y0 (S y1)) \/ (~ (Peano.lt y0 y1))).
Definition term190 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term185 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1))).
Definition term148 := forall y0 : nat, forall y1 : nat, ((Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ ((~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term133 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term128 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0)).
Definition term87 := forall y0 : nat, forall y1 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ ((Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term47 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term16 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term28 := (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> ~ (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)).
Definition term36 (x0 : nat -> Prop) := @eq Prop (@FINITE nat x0).
Definition term350 (x0 : type994) (x1 : nat -> Prop) := (~ (@FINITE nat x1)) \/ (forall y0 : nat, (~ (@IN nat y0 x1)) \/ (Peano.le y0 (x0 x1))).
Definition term276 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term290 (x0 : nat -> Prop) := fun y0 : nat -> nat => (@FINITE nat x0) \/ (forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))).
Definition term201 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (@IN nat y0 x0) -> Peano.le y0 x1) x2).
Definition term66 (x0 : nat -> Prop) := (@FINITE nat x0) /\ (forall y0 : nat, @IN nat y0 x0).
Definition term368 := and (exists y0 : type992, (fun y1 : type992 => forall y2 : nat -> Prop, (@FINITE nat y2) \/ (forall y3 : nat, (@IN nat (y1 y2 y3) y2) /\ (~ (Peano.le (y1 y2 y3) y3)))) y0).
Definition term179 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))) x0).
Definition term122 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) x0).
Definition term360 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term291 (x0 : nat -> Prop) := exists y0 : nat -> nat, (@FINITE nat x0) \/ (forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))).
Definition term216 (x0 : nat -> Prop) := or (~ (@FINITE nat x0)).
Definition term363 := (exists y0 : type992, (fun y1 : type992 => forall y2 : nat -> Prop, (@FINITE nat y2) \/ (forall y3 : nat, (@IN nat (y1 y2 y3) y2) /\ (~ (Peano.le (y1 y2 y3) y3)))) y0) /\ (exists y0 : type994, forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1)))).
Definition term55 (x0 : nat -> Prop) := ~ (ex x0).
Definition term354 (x0 : type994) := forall y0 : nat -> Prop, (~ (@FINITE nat y0)) \/ (forall y1 : nat, (~ (@IN nat y1 y0)) \/ (Peano.le y1 (x0 y0))).
Definition term446 (x0 : nat -> Prop) := (~ (@FINITE nat x0)) -> @FINITE nat x0.
Definition term45 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term63 (x0 : nat -> Prop) := forall y0 : nat, @IN nat y0 x0.
Definition term6 := (((~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False) -> (~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False) -> (~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False.
Definition term321 (x0 : nat -> Prop) := exists y0 : nat, (~ (@FINITE nat x0)) \/ ((fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0).
Definition term79 (x0 : nat) (x1 : nat) := (~ (~ (Peano.lt x1 x0))) \/ (Peano.le x0 x1).
Definition term25 := ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> ~ (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)).
Definition term81 (x0 : nat) (x1 : nat) := and ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term303 (x0 : nat -> Prop) := exists y0 : nat -> nat, (fun y1 : nat -> Prop => fun y2 : nat -> nat => (@FINITE nat y1) \/ (forall y3 : nat, (@IN nat (y2 y3) y1) /\ (~ (Peano.le (y2 y3) y3)))) x0 y0.
Definition term371 (x0 : type992) := and ((fun y0 : type992 => forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (y0 y1 y2) y1) /\ (~ (Peano.le (y0 y1 y2) y2)))) x0).
Definition term329 (x0 : nat -> Prop) (x1 : nat) := (~ (@FINITE nat x0)) \/ (forall y0 : nat, (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1)).
Definition term38 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term362 (x0 : type251) (x1 : Prop) := exists y0 : type992, (x0 y0) /\ x1.
Definition term436 (x0 : nat) (x1 : nat) := (~ (~ (x0 = x1))) -> Peano.lt x0 (S x1).
Definition term343 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat -> Prop => fun y2 : nat => (~ (@FINITE nat y1)) \/ (forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2))) x0 y0.
Definition term238 := fun y0 : nat -> Prop => ((fun y1 : nat -> Prop => (@FINITE nat y1) \/ (forall y2 : nat, exists y3 : nat, (@IN nat y3 y1) /\ (~ (Peano.le y3 y2)))) y0) /\ ((fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (exists y2 : nat, forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2))) y0).
Definition term400 (x0 : type992) (x1 : nat -> Prop) := fun y0 : nat => (@IN nat (x0 x1 y0) x1) /\ (~ (Peano.le (x0 x1 y0) y0)).
Definition term21 := (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False.
Definition term56 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term477 (x0 : nat) (x1 : nat) := ~ ((Peano.lt x1 x0) /\ (Peano.le x0 x1)).
Definition term470 (x0 : type994) (x1 : nat -> Prop) := (@FINITE nat x1) /\ (@IN nat (S (x0 x1)) x1).
Definition term246 := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (exists y2 : nat, forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2))) y0.
Definition term241 := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => (@FINITE nat y1) \/ (forall y2 : nat, exists y3 : nat, (@IN nat y3 y1) /\ (~ (Peano.le y3 y2)))) y0.
Definition term41 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term54 (x0 : nat) (x1 : nat -> Prop) := ~ (~ (@IN nat x0 x1)).
Definition term302 (x0 : nat -> Prop) := fun y0 : nat -> nat => (fun y1 : nat -> Prop => fun y2 : nat -> nat => (@FINITE nat y1) \/ (forall y3 : nat, (@IN nat (y2 y3) y1) /\ (~ (Peano.le (y2 y3) y3)))) x0 y0.
Definition term2 := (~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> False.
Definition term67 (x0 : nat -> Prop) := ~ ((@FINITE nat x0) -> exists y0 : nat, ~ (@IN nat y0 x0)).
Definition term239 := @eq Prop (forall y0 : nat -> Prop, ((fun y1 : nat -> Prop => (@FINITE nat y1) \/ (forall y2 : nat, exists y3 : nat, (@IN nat y3 y1) /\ (~ (Peano.le y3 y2)))) y0) /\ ((fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (exists y2 : nat, forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2))) y0)).
Definition term211 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (@IN nat y2 x0) -> Peano.le y2 y1) y0).
Definition term138 (x0 : nat) (x1 : nat) := or (Peano.lt x0 (S x1)).
Definition term52 (x0 : nat -> Prop) := (@FINITE nat x0) -> exists y0 : nat, ~ (@IN nat y0 x0).
Definition term261 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (@IN nat y2 x0) /\ (~ (Peano.le y2 y1))) x1 y0.
Definition term157 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) x1) /\ ((fun y0 : nat => (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))) x1).
Definition term100 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1) /\ ((fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0)) x1).
Definition term91 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term235 (x0 : nat -> Prop) := and ((fun y0 : nat -> Prop => (@FINITE nat y0) \/ (forall y1 : nat, exists y2 : nat, (@IN nat y2 y0) /\ (~ (Peano.le y2 y1)))) x0).
Definition term345 := fun y0 : nat -> Prop => exists y1 : nat, (fun y2 : nat -> Prop => fun y3 : nat => (~ (@FINITE nat y2)) \/ (forall y4 : nat, (~ (@IN nat y4 y2)) \/ (Peano.le y4 y3))) y0 y1.
Definition term432 (x0 : type994) (x1 : nat -> Prop) := (~ ((x0 x1) = (x0 x1))) -> (x0 x1) = (x0 x1).
Definition term288 (x0 : nat -> Prop) (x1 : nat -> nat) := (@FINITE nat x0) \/ (forall y0 : nat, (@IN nat (x1 y0) x0) /\ (~ (Peano.le (x1 y0) y0))).
Definition term341 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat -> Prop => fun y1 : nat => (~ (@FINITE nat y0)) \/ (forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1))) x0 x1.
Definition term75 := exists y0 : nat -> Prop, (@FINITE nat y0) /\ (forall y1 : nat, @IN nat y1 y0).
Definition term143 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (S x1)) \/ (~ ((x0 = x1) \/ (Peano.lt x0 x1)))) /\ ((~ (Peano.lt x0 (S x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1))).
Definition term480 (x0 : type994) (x1 : nat -> Prop) := (Peano.lt (x0 x1) (S (x0 x1))) /\ (Peano.le (S (x0 x1)) (x0 x1)).
Definition term301 (x0 : nat -> Prop) (x1 : nat -> nat) := (fun y0 : nat -> nat => (@FINITE nat x0) \/ (forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1)))) x1.
Definition term384 (x0 : type994) := (fun y0 : type994 => forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1)))) x0.
Definition term365 (x0 : type992) := (fun y0 : type992 => forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (y0 y1 y2) y1) /\ (~ (Peano.le (y0 y1 y2) y2)))) x0.
Definition term135 (x0 : nat) (x1 : nat) := ~ ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term430 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt x0 (S y0)) \/ (~ (x0 = y0))) /\ ((Peano.lt x0 (S y0)) \/ (~ (Peano.lt x0 y0)))) x1.
Definition term383 (x0 : type992) := exists y0 : type994, (forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (x0 y1 y2) y1) /\ (~ (Peano.le (x0 y1 y2) y2)))) /\ ((fun y1 : type994 => forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))) y0).
Definition term144 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (S x1)) \/ ((~ (x0 = x1)) /\ (~ (Peano.lt x0 x1)))) /\ ((~ (Peano.lt x0 (S x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1))).
Definition term455 (x0 : type994) (x1 : nat) (x2 : nat -> Prop) := (Peano.le x1 (x0 x2)) \/ ((~ (@FINITE nat x2)) \/ (~ (@IN nat x1 x2))).
Definition term426 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => @IN nat y0 x0) x1.
Definition term169 (x0 : nat) := (forall y0 : nat, (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ (forall y0 : nat, (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))).
Definition term112 (x0 : nat) := (forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ (forall y0 : nat, (Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term137 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 (S x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term366 := fun y0 : type992 => (fun y1 : type992 => forall y2 : nat -> Prop, (@FINITE nat y2) \/ (forall y3 : nat, (@IN nat (y1 y2 y3) y2) /\ (~ (Peano.le (y1 y2 y3) y3)))) y0.
Definition term8 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term187 := and (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))).
Definition term130 := and (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))).
Definition term353 (x0 : type994) := forall y0 : nat -> Prop, (fun y1 : nat -> Prop => fun y2 : nat => (~ (@FINITE nat y1)) \/ (forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2))) y0 (x0 y0).
Definition term312 (x0 : type992) := forall y0 : nat -> Prop, (fun y1 : nat -> Prop => fun y2 : nat -> nat => (@FINITE nat y1) \/ (forall y3 : nat, (@IN nat (y2 y3) y1) /\ (~ (Peano.le (y2 y3) y3)))) y0 (x0 y0).
Definition term43 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term313 (x0 : type992) := forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, (@IN nat (x0 y0 y1) y0) /\ (~ (Peano.le (x0 y0 y1) y1))).
Definition term243 := forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, exists y2 : nat, (@IN nat y2 y0) /\ (~ (Peano.le y2 y1))).
Definition term398 (x0 : type994) (x1 : nat -> Prop) := forall y0 : nat, (~ (@IN nat y0 x1)) \/ (Peano.le y0 (x0 x1)).
Definition term419 (x0 : type994) := forall y0 : nat -> Prop, forall y1 : nat, (~ (@FINITE nat y0)) \/ ((~ (@IN nat y1 y0)) \/ (Peano.le y1 (x0 y0))).
Definition term361 (x0 : type251) (x1 : Prop) := (exists y0 : type992, x0 y0) /\ x1.
Definition term163 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0))).
Definition term364 := exists y0 : type992, ((fun y1 : type992 => forall y2 : nat -> Prop, (@FINITE nat y2) \/ (forall y3 : nat, (@IN nat (y1 y2 y3) y2) /\ (~ (Peano.le (y1 y2 y3) y3)))) y0) /\ (exists y1 : type994, forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))).
Definition term168 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term208 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (@IN nat y2 x0) -> Peano.le y2 y1) y0).
Definition term58 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => ~ (@IN nat y1 x0)) y0).
Definition term324 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0.
Definition term188 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0.
Definition term183 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0.
Definition term131 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term126 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0.
Definition term299 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => fun y1 : nat -> nat => (@FINITE nat y0) \/ (forall y2 : nat, (@IN nat (y1 y2) y0) /\ (~ (Peano.le (y1 y2) y2)))) x0.
Definition term300 (x0 : nat -> Prop) (x1 : nat -> nat) := (fun y0 : nat -> Prop => fun y1 : nat -> nat => (@FINITE nat y0) \/ (forall y2 : nat, (@IN nat (y1 y2) y0) /\ (~ (Peano.le (y1 y2) y2)))) x0 x1.
Definition term429 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt y0 (S y1)) \/ (~ (y0 = y1))) /\ ((Peano.lt y0 (S y1)) \/ (~ (Peano.lt y0 y1)))) x0.
Definition term178 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term176 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) x0.
Definition term121 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term119 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0.
Definition term270 (x0 : nat -> Prop) (x1 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (@IN nat y2 x0) /\ (~ (Peano.le y2 y1))) y0 (x1 y0).
Definition term315 := fun y0 : type992 => forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (y0 y1 y2) y1) /\ (~ (Peano.le (y0 y1 y2) y2))).
Definition term149 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, ((Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ ((~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term18 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term414 (x0 : nat) (x1 : type994) (x2 : nat -> Prop) := (~ (@FINITE nat x2)) \/ ((~ (@IN nat x0 x2)) \/ (Peano.le x0 (x1 x2))).
Definition term481 (x0 : type994) (x1 : nat -> Prop) := ((Peano.lt (x0 x1) (S (x0 x1))) /\ (Peano.le (S (x0 x1)) (x0 x1))) -> False.
Definition term200 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 x0) -> Peano.le y0 x1) x2.
Definition term59 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (@IN nat y0 x0)) x1.
Definition term139 (x0 : nat) (x1 : nat) := (Peano.lt x0 (S x1)) \/ (~ ((x0 = x1) \/ (Peano.lt x0 x1))).
Definition term10 := fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False.
Definition term106 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0)).
Definition term311 (x0 : type992) := fun y0 : nat -> Prop => (@FINITE nat y0) \/ (forall y1 : nat, (@IN nat (x0 y0 y1) y0) /\ (~ (Peano.le (x0 y0 y1) y1))).
Definition term232 := fun y0 : nat -> Prop => (@FINITE nat y0) \/ (forall y1 : nat, exists y2 : nat, (@IN nat y2 y0) /\ (~ (Peano.le y2 y1))).
Definition term207 (x0 : nat -> Prop) := ~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0).
Definition term4 := (~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) -> False.
Definition term415 (x0 : type994) (x1 : nat -> Prop) := fun y0 : nat => (~ (@FINITE nat x1)) \/ ((fun y1 : nat => (~ (@IN nat y1 x1)) \/ (Peano.le y1 (x0 x1))) y0).
Definition term156 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term266 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 x0) /\ (~ (Peano.le y0 x2))) (x1 x2).
Definition term205 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1).
Definition term231 := (forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (@FINITE nat y1) \/ (forall y2 : nat, exists y3 : nat, (@IN nat y3 y1) /\ (~ (Peano.le y3 y2)))) y0) /\ (forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (exists y2 : nat, forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2))) y0).
Definition term199 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (@IN nat y1 x0) -> Peano.le y1 x1) y0).
Definition term219 (x0 : nat -> Prop) := or (@FINITE nat x0).
Definition term405 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 \/ (x1 y0).
Definition term262 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (@IN nat y3 x0) /\ (~ (Peano.le y3 y2))) y0 y1.
Definition term109 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0.
Definition term186 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0).
Definition term164 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0).
Definition term129 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0).
Definition term107 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0).
Definition term464 (x0 : nat -> Prop) := ~ (~ (@FINITE nat x0)).
Definition term177 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) x0).
Definition term120 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0).
Definition term423 (x0 : nat) := forall y0 : nat, ((Peano.lt x0 (S y0)) \/ (~ (x0 = y0))) /\ ((Peano.lt x0 (S y0)) \/ (~ (Peano.lt x0 y0))).
Definition term82 (x0 : nat) (x1 : nat) := ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))) /\ ((~ (~ (Peano.lt x1 x0))) \/ (Peano.le x0 x1)).
Definition term145 (x0 : nat) := fun y0 : nat => ((Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ ((~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))).
Definition term376 := fun y0 : type992 => (forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (y0 y1 y2) y1) /\ (~ (Peano.le (y0 y1 y2) y2)))) /\ (exists y1 : type994, forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))).
Definition term51 (x0 : nat -> Prop) := imp (@FINITE nat x0).
Definition term77 (x0 : nat) (x1 : nat) := or (~ (~ (Peano.lt x0 x1))).
Definition term71 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) x0.
Definition term117 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0)).
Definition term298 := fun y0 : nat -> Prop => fun y1 : nat -> nat => (@FINITE nat y0) \/ (forall y2 : nat, (@IN nat (y1 y2) y0) /\ (~ (Peano.le (y1 y2) y2))).
Definition term244 := and (forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (@FINITE nat y1) \/ (forall y2 : nat, exists y3 : nat, (@IN nat y3 y1) /\ (~ (Peano.le y3 y2)))) y0).
Definition term388 (x0 : type992) := @eq Prop ((forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, (@IN nat (x0 y0 y1) y0) /\ (~ (Peano.le (x0 y0 y1) y1)))) /\ (exists y0 : type994, forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1))))).
Definition term387 (x0 : type992) := @eq Prop ((forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, (@IN nat (x0 y0 y1) y0) /\ (~ (Peano.le (x0 y0 y1) y1)))) /\ (exists y0 : type994, (fun y1 : type994 => forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))) y0)).
Definition term64 (x0 : nat -> Prop) := and (@FINITE nat x0).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term325 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0.
Definition term171 := forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term114 := forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term275 (x0 : nat -> Prop) := (@FINITE nat x0) \/ (exists y0 : nat -> nat, forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))).
Definition term69 (x0 : type993) := exists y0 : nat -> Prop, ~ (x0 y0).
Definition term155 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) x1).
Definition term98 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1).
Definition term202 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (@IN nat y1 x0) -> Peano.le y1 x1) y0).
Definition term468 (x0 : nat) (x1 : nat -> Prop) := imp ((@FINITE nat x1) /\ (@IN nat x0 x1)).
Definition term65 (x0 : nat -> Prop) := (@FINITE nat x0) /\ (~ (exists y0 : nat, ~ (@IN nat y0 x0))).
Definition term359 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term224 (x0 : nat -> Prop) := ((@FINITE nat x0) \/ (~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0))) /\ ((~ (@FINITE nat x0)) \/ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)).
Definition term473 (x0 : type994) (x1 : nat -> Prop) := (~ (Peano.le (S (x0 x1)) (x0 x1))) -> Peano.le (S (x0 x1)) (x0 x1).
Definition term227 := forall y0 : nat -> Prop, ((@FINITE nat y0) \/ (forall y1 : nat, exists y2 : nat, (@IN nat y2 y0) /\ (~ (Peano.le y2 y1)))) /\ ((~ (@FINITE nat y0)) \/ (exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1))).
Definition term444 (x0 : type994) (x1 : nat -> Prop) := (~ (Peano.lt (x0 x1) (S (x0 x1)))) -> Peano.lt (x0 x1) (S (x0 x1)).
Definition term438 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term195 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (@IN nat x1 x0)) \/ (Peano.le x1 x2).
Definition term331 (x0 : nat -> Prop) := fun y0 : nat => (~ (@FINITE nat x0)) \/ (forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)).
Definition term72 (x0 : nat -> Prop) := ~ ((fun y0 : nat -> Prop => (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0)) x0).
Definition term189 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0.
Definition term184 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0.
Definition term132 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term127 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0.
Definition term251 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term26 := imp (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)).
Definition term193 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ ((@IN nat x1 x0) -> Peano.le x1 x2).
Definition term203 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (@IN nat y0 x0) /\ (~ (Peano.le y0 x1)).
Definition term442 (x0 : type994) (x1 : nat -> Prop) := ((x0 x1) = (x0 x1)) -> Peano.lt (x0 x1) (S (x0 x1)).
Definition term230 := forall y0 : nat -> Prop, ((fun y1 : nat -> Prop => (@FINITE nat y1) \/ (forall y2 : nat, exists y3 : nat, (@IN nat y3 y1) /\ (~ (Peano.le y3 y2)))) y0) /\ ((fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (exists y2 : nat, forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2))) y0).
Definition term225 (x0 : nat -> Prop) := ((@FINITE nat x0) \/ (forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0)))) /\ ((~ (@FINITE nat x0)) \/ (exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0))).
Definition term197 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term441 (x0 : nat) (x1 : nat) := (x0 = x1) -> Peano.lt x0 (S x1).
Definition term318 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term334 := forall y0 : nat -> Prop, exists y1 : nat, (~ (@FINITE nat y0)) \/ (forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1)).
Definition term293 := forall y0 : nat -> Prop, exists y1 : nat -> nat, (@FINITE nat y0) \/ (forall y2 : nat, (@IN nat (y1 y2) y0) /\ (~ (Peano.le (y1 y2) y2))).
Definition term292 := fun y0 : nat -> Prop => exists y1 : nat -> nat, (@FINITE nat y0) \/ (forall y2 : nat, (@IN nat (y1 y2) y0) /\ (~ (Peano.le (y1 y2) y2))).
Definition term229 (x0 : type993) (x1 : type993) := (forall y0 : nat -> Prop, x0 y0) /\ (forall y0 : nat -> Prop, x1 y0).
Definition term452 (x0 : nat) (x1 : type994) (x2 : nat -> Prop) := Peano.le x0 (x1 x2).
Definition term96 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1.
Definition term424 := fun y0 : nat => forall y1 : nat, ((Peano.lt y0 (S y1)) \/ (~ (y0 = y1))) /\ ((Peano.lt y0 (S y1)) \/ (~ (Peano.lt y0 y1))).
Definition term175 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term174 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1))).
Definition term147 := fun y0 : nat => forall y1 : nat, ((Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ ((~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term86 := fun y0 : nat => forall y1 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ ((Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term42 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term392 (x0 : type992) := fun y0 : type994 => (forall y1 : nat -> Prop, (@FINITE nat y1) \/ (forall y2 : nat, (@IN nat (x0 y1 y2) y1) /\ (~ (Peano.le (x0 y1 y2) y2)))) /\ (forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (forall y2 : nat, (~ (@IN nat y2 y1)) \/ (Peano.le y2 (y0 y1)))).
Definition term146 (x0 : nat) := forall y0 : nat, ((Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ ((~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))).
Definition term29 := imp (~ (forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, ~ (@IN nat y1 y0))).
Definition term407 (x0 : type994) (x1 : nat -> Prop) := forall y0 : nat, (~ (@FINITE nat x1)) \/ ((fun y1 : nat => (~ (@IN nat y1 x1)) \/ (Peano.le y1 (x0 x1))) y0).
Definition term385 := fun y0 : type994 => (fun y1 : type994 => forall y2 : nat -> Prop, (~ (@FINITE nat y2)) \/ (forall y3 : nat, (~ (@IN nat y3 y2)) \/ (Peano.le y3 (y1 y2)))) y0.
Definition term416 (x0 : type994) (x1 : nat -> Prop) := fun y0 : nat => (~ (@FINITE nat x1)) \/ ((~ (@IN nat y0 x1)) \/ (Peano.le y0 (x0 x1))).
Definition term372 (x0 : type992) := and (forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, (@IN nat (x0 y0 y1) y0) /\ (~ (Peano.le (x0 y0 y1) y1)))).
Definition term245 := and (forall y0 : nat -> Prop, (@FINITE nat y0) \/ (forall y1 : nat, exists y2 : nat, (@IN nat y2 y0) /\ (~ (Peano.le y2 y1)))).
Definition term194 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x1 x0) /\ (~ (Peano.le x1 x2)).
Definition term80 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) \/ (Peano.le x0 x1).
Definition term439 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
