Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term252 (x0 : nat -> nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1)))) y0.
Definition term47 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (Peano.le x0 y0) /\ (@IN nat y0 x1).
Definition term123 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (@IN nat (x1 x2) x0) /\ (~ (Peano.le (x1 x2) x2)).
Definition term6 (x0 : nat -> Prop) := @eq Prop (@INFINITE nat x0).
Definition term127 (x0 : nat -> Prop) (x1 : nat -> nat) := forall y0 : nat, (@IN nat (x1 y0) x0) /\ (~ (Peano.le (x1 y0) y0)).
Definition term392 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term332 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0).
Definition term56 (x0 : nat -> Prop) := ~ (all x0).
Definition term439 := (~ False) -> False.
Definition term453 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (S x1) (x0 (S x1)))) -> Peano.le (S x1) (x0 (S x1)).
Definition term278 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat -> nat, (fun y1 : nat -> nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 x0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))) y0.
Definition term14 (x0 : nat -> Prop) := (((~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term450 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (x0 (S x1)) x1)) -> Peano.le (x0 (S x1)) x1.
Definition term315 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0)).
Definition term412 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := (~ (@IN nat (x0 x1) x2)) -> @IN nat (x0 x1) x2.
Definition term101 (x0 : nat -> Prop) := (forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))) /\ (exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x0))).
Definition term384 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term361 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term324 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0).
Definition term299 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0).
Definition term93 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x0)).
Definition term76 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0).
Definition term1 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0.
Definition term96 (x0 : nat -> Prop) := (~ (~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0))) /\ (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)).
Definition term169 (x0 : nat -> Prop) := exists y0 : nat -> nat, exists y1 : nat, (forall y2 : nat, (@IN nat (y0 y2) x0) /\ (~ (Peano.le (y0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0))).
Definition term261 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := or ((forall y0 : nat, (@IN nat (x0 y0) x2) /\ (~ (Peano.le (x0 y0) y0))) /\ (forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (@IN nat y0 x2)))).
Definition term268 (x0 : nat -> nat) (x1 : nat -> Prop) := @eq Prop ((fun y0 : Prop => y0 = (exists y1 : nat, ((forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1)))) \/ (exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x1)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x1))))) ((exists y0 : nat, (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) \/ (exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))))).
Definition term50 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (@IN nat y0 x0) -> Peano.le y0 x1.
Definition term418 (x0 : Prop) := ~ (~ x0).
Definition term195 (x0 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0) /\ (exists y1 : nat -> nat, forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0)).
Definition term137 (x0 : nat -> Prop) := (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0) /\ (exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x0))).
Definition term436 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 x1) x1.
Definition term95 (x0 : nat -> Prop) := and (exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)).
Definition term149 (x0 : nat -> Prop) := fun y0 : nat -> nat => ((fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0) /\ (exists y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0))).
Definition term426 (x0 : nat -> nat) (x1 : nat) := Peano.le x1 (x0 x1).
Definition term276 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := (fun y0 : nat -> nat => (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 x0)) /\ (forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x1))) x2.
Definition term282 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat -> Prop) := ((forall y0 : nat, (@IN nat (x0 y0) x3) /\ (~ (Peano.le (x0 y0) y0))) /\ (forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (@IN nat y0 x3)))) \/ ((forall y0 : nat, (~ (@IN nat y0 x3)) \/ (Peano.le y0 x1)) /\ (forall y0 : nat, (Peano.le y0 (x2 y0)) /\ (@IN nat (x2 y0) x3))).
Definition term181 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (Peano.le y0 y1) /\ (@IN nat y1 x0)) x2 (x1 x2).
Definition term121 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))) x2 (x1 x2).
Definition term131 (x0 : nat -> Prop) := and (exists y0 : nat -> nat, forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))).
Definition term171 (x0 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.le y2 y3) /\ (@IN nat y3 x0)) y0 y1.
Definition term110 (x0 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (@IN nat y3 x0) /\ (~ (Peano.le y3 y2))) y0 y1.
Definition term108 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term74 (x0 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0)).
Definition term8 (x0 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0).
Definition term472 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.lt x0 x1).
Definition term370 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term310 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0).
Definition term32 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term242 (x0 : nat -> Prop) := fun y0 : nat -> nat => ((fun y1 : nat -> nat => exists y2 : nat, (forall y3 : nat, (@IN nat (y1 y3) x0) /\ (~ (Peano.le (y1 y3) y3))) /\ (forall y3 : nat, (~ (Peano.le y2 y3)) \/ (~ (@IN nat y3 x0)))) y0) \/ (exists y1 : nat, exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x0)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x0))).
Definition term98 (x0 : nat -> Prop) := and (~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)).
Definition term7 (x0 : nat -> Prop) := @eq Prop (~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)).
Definition term239 (x0 : nat -> nat) (x1 : nat -> Prop) := or (exists y0 : nat, (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))).
Definition term251 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) x2.
Definition term424 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le x1 (x0 x1)).
Definition term245 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term24 := (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term440 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat (x0 (S x1)) x2.
Definition term447 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (@IN nat (x1 (S x2)) x0) -> Peano.le (x1 (S x2)) x2.
Definition term345 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (Peano.le x0 y0).
Definition term280 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop (((forall y0 : nat, (@IN nat (x0 y0) x2) /\ (~ (Peano.le (x0 y0) y0))) /\ (forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (@IN nat y0 x2)))) \/ (exists y0 : nat -> nat, (forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x1)) /\ (forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x2)))).
Definition term279 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop (((forall y0 : nat, (@IN nat (x0 y0) x2) /\ (~ (Peano.le (x0 y0) y0))) /\ (forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (@IN nat y0 x2)))) \/ (exists y0 : nat -> nat, (fun y1 : nat -> nat => (forall y2 : nat, (~ (@IN nat y2 x2)) \/ (Peano.le y2 x1)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x2))) y0)).
Definition term443 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (Peano.le x1 x0) \/ (~ (@IN nat x1 x2)).
Definition term153 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term9 (x0 : Prop) := (~ x0) -> False.
Definition term385 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term362 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term325 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0).
Definition term300 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0).
Definition term403 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term343 := (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)).
Definition term358 (x0 : nat) := forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term292 (x0 : nat) := forall y0 : nat, ((Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) /\ ((~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0)).
Definition term226 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term90 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)) x1).
Definition term71 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0) x1).
Definition term64 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (@IN nat y0 x0) /\ (~ (Peano.le y0 x1)).
Definition term168 (x0 : nat -> Prop) := fun y0 : nat -> nat => exists y1 : nat, (forall y2 : nat, (@IN nat (y0 y2) x0) /\ (~ (Peano.le (y0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0))).
Definition term267 (x0 : nat -> nat) (x1 : nat -> Prop) := (fun y0 : Prop => y0 = (exists y1 : nat, ((forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1)))) \/ (exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x1)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x1))))) ((exists y0 : nat, (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) \/ (exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1)))).
Definition term277 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat -> nat => (fun y1 : nat -> nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 x0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))) y0.
Definition term379 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term374 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term319 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0.
Definition term314 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0.
Definition term366 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1)).
Definition term209 (x0 : Prop) (x1 : type1002) := x0 /\ (exists y0 : nat -> nat, x1 y0).
Definition term175 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (Peano.le y0 y1) /\ (@IN nat y1 x0)) x1 x2.
Definition term114 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))) x1 x2.
Definition term368 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1.
Definition term28 := fun y0 : nat -> Prop => (~ ((~ (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) = (forall y1 : nat, exists y2 : nat, (Peano.le y1 y2) /\ (@IN nat y2 y0)))) -> (forall y1 : nat, forall y2 : nat, (Peano.le (S y1) y2) = (Peano.lt y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)).
Definition term415 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term204 (x0 : nat) (x1 : nat -> Prop) := ((fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) x0) /\ (exists y0 : nat -> nat, forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x1)).
Definition term297 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term170 (x0 : nat -> Prop) := or (exists y0 : nat -> nat, exists y1 : nat, (forall y2 : nat, (@IN nat (y0 y2) x0) /\ (~ (Peano.le (y0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0)))).
Definition term125 (x0 : nat -> Prop) (x1 : nat -> nat) := fun y0 : nat => (@IN nat (x1 y0) x0) /\ (~ (Peano.le (x1 y0) y0)).
Definition term222 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat -> nat, (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 x0)) /\ (forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x1)).
Definition term58 (x0 : nat -> Prop) (x1 : nat) := ~ (forall y0 : nat, (@IN nat y0 x0) -> Peano.le y0 x1).
Definition term183 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := (Peano.le x1 (x0 x1)) /\ (@IN nat (x0 x1) x2).
Definition term94 (x0 : nat -> Prop) := and (~ (~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0))).
Definition term382 := fun y0 : nat => (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term322 := fun y0 : nat => (forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)).
Definition term166 (x0 : nat -> nat) (x1 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1))).
Definition term87 (x0 : nat -> Prop) := ~ (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)).
Definition term17 := ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term228 (x0 : type1002) (x1 : Prop) := (exists y0 : nat -> nat, x0 y0) \/ x1.
Definition term289 (x0 : nat -> Prop) := exists y0 : nat -> nat, exists y1 : nat, exists y2 : nat -> nat, ((forall y3 : nat, (@IN nat (y0 y3) x0) /\ (~ (Peano.le (y0 y3) y3))) /\ (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (@IN nat y3 x0)))) \/ ((forall y3 : nat, (~ (@IN nat y3 x0)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x0))).
Definition term152 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (Peano.le x0 x1) /\ (@IN nat x1 x2).
Definition term12 (x0 : nat -> Prop) := (~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term408 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1)) x2.
Definition term468 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term244 (x0 : nat -> Prop) := exists y0 : nat -> nat, (exists y1 : nat, (forall y2 : nat, (@IN nat (y0 y2) x0) /\ (~ (Peano.le (y0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0)))) \/ (exists y1 : nat, exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x0)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x0))).
Definition term414 (x0 : Prop) := (~ x0) -> x0.
Definition term100 (x0 : nat -> Prop) := (~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) /\ (~ (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0))).
Definition term458 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt x0 x1) \/ (~ (Peano.le (S x0) x1))).
Definition term474 (x0 : nat -> nat) (x1 : nat) := ((Peano.le (x0 (S x1)) x1) /\ (Peano.lt x1 (x0 (S x1)))) -> False.
Definition term273 (x0 : Prop) (x1 : type1002) := exists y0 : nat -> nat, x0 \/ (x1 y0).
Definition term423 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (@IN nat (x1 x2) x0) -> ~ (Peano.le x2 (x1 x2)).
Definition term112 (x0 : nat -> Prop) := fun y0 : nat => fun y1 : nat => (@IN nat y1 x0) /\ (~ (Peano.le y1 y0)).
Definition term302 (x0 : nat) := fun y0 : nat => (~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0).
Definition term306 (x0 : nat) (x1 : nat) := and ((Peano.le (S x0) x1) \/ (~ (Peano.lt x0 x1))).
Definition term73 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0)).
Definition term106 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term205 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, (~ (@IN nat y0 x1)) \/ (Peano.le y0 x0)) /\ (exists y0 : nat -> nat, forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x1)).
Definition term432 (x0 : nat -> nat) (x1 : nat) := (Peano.lt x1 (x0 x1)) -> ~ (Peano.lt x1 (x0 x1)).
Definition term304 (x0 : nat) (x1 : nat) := (Peano.le (S x0) x1) \/ (~ (Peano.lt x0 x1)).
Definition term199 (x0 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0).
Definition term363 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term357 (x0 : nat) := fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term184 (x0 : nat -> Prop) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (Peano.le y1 y2) /\ (@IN nat y2 x0)) y0 (x1 y0).
Definition term124 (x0 : nat -> Prop) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (@IN nat y2 x0) /\ (~ (Peano.le y2 y1))) y0 (x1 y0).
Definition term23 := (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term469 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term394 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0))).
Definition term393 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0)).
Definition term372 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0))).
Definition term371 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0)).
Definition term334 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1))).
Definition term333 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0)).
Definition term312 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) /\ ((~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0))).
Definition term311 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0)).
Definition term165 (x0 : nat -> nat) (x1 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1))) y0).
Definition term48 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0).
Definition term190 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x0).
Definition term172 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.le y2 y3) /\ (@IN nat y3 x0)) y1 (y0 y1).
Definition term130 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1)).
Definition term111 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (@IN nat y3 x0) /\ (~ (Peano.le y3 y2))) y1 (y0 y1).
Definition term109 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term281 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat -> nat) := ((forall y0 : nat, (@IN nat (x0 y0) x2) /\ (~ (Peano.le (x0 y0) y0))) /\ (forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (@IN nat y0 x2)))) \/ ((fun y0 : nat -> nat => (forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x1)) /\ (forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x2))) x3).
Definition term296 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term405 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (Peano.le x0 y0)) x1.
Definition term307 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0)) x1.
Definition term185 (x0 : nat -> nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.le y0 (x0 y0)) /\ (@IN nat (x0 y0) x1).
Definition term208 (x0 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) /\ (exists y1 : nat -> nat, forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0)).
Definition term20 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term36 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) -> Peano.le x0 y0.
Definition term82 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (Peano.le x0 y0) /\ (@IN nat y0 x1)) x2.
Definition term113 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))) x1.
Definition term104 (x0 : nat -> Prop) := ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) /\ (~ (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) \/ ((~ (~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0))) /\ (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0))).
Definition term256 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x0)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x0))) y0.
Definition term449 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 (S x1)) x1.
Definition term269 (x0 : nat -> nat) (x1 : nat -> Prop) := @eq Prop (((exists y0 : nat, (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) \/ (exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1)))) = (exists y0 : nat, ((forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) \/ (exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))))).
Definition term467 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.lt x1 (x0 (S x1))).
Definition term151 (x0 : nat -> Prop) := exists y0 : nat -> nat, (forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))) /\ (exists y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0))).
Definition term196 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) x1.
Definition term158 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x0))) x1.
Definition term70 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0) x1.
Definition term434 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) -> Peano.le x0 x1.
Definition term425 (x0 : nat -> nat) (x1 : nat) := (Peano.le x1 (x0 x1)) -> ~ (Peano.le x1 (x0 x1)).
Definition term97 (x0 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) /\ (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)).
Definition term433 (x0 : nat -> nat) (x1 : nat) := Peano.lt x1 (x0 x1).
Definition term210 (x0 : Prop) (x1 : type1002) := exists y0 : nat -> nat, x0 /\ (x1 y0).
Definition term355 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1)).
Definition term387 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term347 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.le y0 y1).
Definition term327 := fun y0 : nat => forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1).
Definition term75 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0).
Definition term52 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0.
Definition term43 := fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term38 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1.
Definition term34 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term191 (x0 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) /\ (exists y0 : nat -> nat, forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x0)).
Definition term213 (x0 : nat -> Prop) (x1 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x0)) x1.
Definition term139 (x0 : nat -> Prop) (x1 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))) x1.
Definition term380 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term455 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) \/ (~ (Peano.le (S x0) x1)).
Definition term272 (x0 : Prop) (x1 : type1002) := x0 \/ (exists y0 : nat -> nat, x1 y0).
Definition term26 (x0 : nat -> Prop) := (~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term4 (x0 : nat -> Prop) := ~ (@FINITE nat x0).
Definition term155 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term442 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := ~ (@IN nat (x0 (S x1)) x2).
Definition term238 (x0 : nat -> Prop) (x1 : nat -> nat) := or ((fun y0 : nat -> nat => exists y1 : nat, (forall y2 : nat, (@IN nat (y0 y2) x0) /\ (~ (Peano.le (y0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0)))) x1).
Definition term352 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1).
Definition term207 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) /\ (exists y1 : nat -> nat, forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0)).
Definition term176 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (Peano.le y1 y2) /\ (@IN nat y2 x0)) x1 y0.
Definition term116 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (@IN nat y2 x0) /\ (~ (Peano.le y2 y1))) x1 y0.
Definition term428 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> ~ (Peano.lt x0 x1).
Definition term413 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := ~ (@IN nat (x0 x1) x2).
Definition term31 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term373 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term313 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0.
Definition term351 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term147 (x0 : nat -> nat) (x1 : nat -> Prop) := ((fun y0 : nat -> nat => forall y1 : nat, (@IN nat (y0 y1) x1) /\ (~ (Peano.le (y0 y1) y1))) x0) /\ (exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1))).
Definition term154 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term27 := fun y0 : nat -> Prop => (~ ((~ (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) = (forall y1 : nat, exists y2 : nat, (Peano.le y1 y2) /\ (@IN nat y2 y0)))) -> (forall y1 : nat, forall y2 : nat, (Peano.le (S y1) y2) = (Peano.lt y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False.
Definition term201 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) /\ (exists y0 : nat -> nat, forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x0))).
Definition term200 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0) /\ (exists y0 : nat -> nat, forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x0))).
Definition term144 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat -> nat, forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))) /\ (exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x0)))).
Definition term143 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0) /\ (exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x0)))).
Definition term249 (x0 : nat -> nat) (x1 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x1)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x1))) y0).
Definition term16 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term49 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x1 x0) -> Peano.le x1 x2.
Definition term218 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := (forall y0 : nat, (~ (@IN nat y0 x1)) \/ (Peano.le y0 x0)) /\ ((fun y0 : nat -> nat => forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x1)) x2).
Definition term189 (x0 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x0).
Definition term188 (x0 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.le y2 y3) /\ (@IN nat y3 x0)) y1 (y0 y1).
Definition term129 (x0 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1)).
Definition term128 (x0 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (@IN nat y3 x0) /\ (~ (Peano.le y3 y2))) y1 (y0 y1).
Definition term284 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat -> nat => ((forall y1 : nat, (@IN nat (x0 y1) x2) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le x1 y1)) \/ (~ (@IN nat y1 x2)))) \/ ((forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x1)) /\ (forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x2))).
Definition term234 (x0 : nat -> Prop) := exists y0 : nat -> nat, (fun y1 : nat -> nat => exists y2 : nat, (forall y3 : nat, (@IN nat (y1 y3) x0) /\ (~ (Peano.le (y1 y3) y3))) /\ (forall y3 : nat, (~ (Peano.le y2 y3)) \/ (~ (@IN nat y3 x0)))) y0.
Definition term215 (x0 : nat -> Prop) := exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0)) y0.
Definition term141 (x0 : nat -> Prop) := exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0.
Definition term103 (x0 : nat -> Prop) := or ((forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))) /\ (exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x0)))).
Definition term66 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1).
Definition term451 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 (S x1)) x1).
Definition term180 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)).
Definition term179 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.le y2 y3) /\ (@IN nat y3 x0)) y0 y1).
Definition term120 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))).
Definition term119 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (@IN nat y3 x0) /\ (~ (Peano.le y3 y2))) y0 y1).
Definition term15 (x0 : nat -> Prop) := (((~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> ((~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term377 (x0 : nat) := and (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))).
Definition term317 (x0 : nat) := and (forall y0 : nat, (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))).
Definition term203 (x0 : nat -> Prop) (x1 : nat) := and (forall y0 : nat, (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1)).
Definition term146 (x0 : nat -> Prop) (x1 : nat -> nat) := and (forall y0 : nat, (@IN nat (x1 y0) x0) /\ (~ (Peano.le (x1 y0) y0))).
Definition term42 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term460 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le (S x0) x1)).
Definition term475 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (~ ((~ (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) = (forall y1 : nat, exists y2 : nat, (Peano.le y1 y2) /\ (@IN nat y2 y0)))) -> (forall y1 : nat, forall y2 : nat, (Peano.le (S y1) y2) = (Peano.lt y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False) x0.
Definition term417 (x0 : nat) (x1 : nat -> Prop) := ~ (@IN nat x0 x1).
Definition term232 (x0 : nat -> Prop) (x1 : nat -> nat) := (fun y0 : nat -> nat => exists y1 : nat, (forall y2 : nat, (@IN nat (y0 y2) x0) /\ (~ (Peano.le (y0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0)))) x1.
Definition term274 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := ((forall y0 : nat, (@IN nat (x0 y0) x2) /\ (~ (Peano.le (x0 y0) y0))) /\ (forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (@IN nat y0 x2)))) \/ (exists y0 : nat -> nat, (fun y1 : nat -> nat => (forall y2 : nat, (~ (@IN nat y2 x2)) \/ (Peano.le y2 x1)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x2))) y0).
Definition term422 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x2 x0) -> ~ (Peano.le x1 x2).
Definition term271 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term214 (x0 : nat -> Prop) := fun y0 : nat -> nat => (fun y1 : nat -> nat => forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0)) y0.
Definition term140 (x0 : nat -> Prop) := fun y0 : nat -> nat => (fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0.
Definition term51 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (@IN nat y0 x0) -> Peano.le y0 x1.
Definition term285 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat -> nat, ((forall y1 : nat, (@IN nat (x0 y1) x2) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le x1 y1)) \/ (~ (@IN nat y1 x2)))) \/ ((forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x1)) /\ (forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x2))).
Definition term187 (x0 : nat -> nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.le y0 (x0 y0)) /\ (@IN nat (x0 y0) x1).
Definition term308 (x0 : nat) (x1 : nat) := (~ (Peano.le (S x0) x1)) \/ (Peano.lt x0 x1).
Definition term471 (x0 : nat) (x1 : nat) := ((Peano.le x1 x0) /\ (Peano.lt x0 x1)) -> False.
Definition term115 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 x0) /\ (~ (Peano.le y0 x1))) x2.
Definition term243 (x0 : nat -> Prop) := fun y0 : nat -> nat => (exists y1 : nat, (forall y2 : nat, (@IN nat (y0 y2) x0) /\ (~ (Peano.le (y0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0)))) \/ (exists y1 : nat, exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x0)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x0))).
Definition term89 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)) x1.
Definition term211 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, (~ (@IN nat y0 x1)) \/ (Peano.le y0 x0)) /\ (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1)) y0).
Definition term402 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term397 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term360 := forall y0 : nat, forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term348 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.le y0 y1).
Definition term342 := forall y0 : nat, forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1).
Definition term337 := forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1)).
Definition term294 := forall y0 : nat, forall y1 : nat, ((Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ ((~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)).
Definition term44 := forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term39 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1.
Definition term18 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term303 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) x1.
Definition term270 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term105 (x0 : nat -> Prop) := ((forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))) /\ (exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x0)))) \/ ((exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) /\ (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0))).
Definition term83 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((fun y0 : nat => (Peano.le x0 y0) /\ (@IN nat y0 x1)) x2).
Definition term61 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (@IN nat y0 x0) -> Peano.le y0 x1) x2).
Definition term142 (x0 : nat -> Prop) := and (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0).
Definition term391 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0).
Definition term331 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)) x0).
Definition term0 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) x0.
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term194 (x0 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0) /\ (exists y0 : nat -> nat, forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x0)).
Definition term67 (x0 : nat -> Prop) := ~ (ex x0).
Definition term33 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term46 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.le x0 y0) /\ (@IN nat y0 x1).
Definition term463 (x0 : nat) (x1 : nat) := (Peano.le (S x0) x1) -> Peano.lt x0 x1.
Definition term241 (x0 : nat -> nat) (x1 : nat -> Prop) := (exists y0 : nat, (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) \/ (exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))).
Definition term250 (x0 : nat -> nat) (x1 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => (forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1)))) y0) \/ ((fun y1 : nat => exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x1)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x1))) y0).
Definition term430 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le x1 (x0 x1))) -> ~ (Peano.lt x1 (x0 x1)).
Definition term354 (x0 : nat) (x1 : nat) := and ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))).
Definition term441 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := (~ (@IN nat (x0 (S x1)) x2)) -> @IN nat (x0 (S x1)) x2.
Definition term221 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat -> nat => (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 x0)) /\ (forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x1)).
Definition term301 (x0 : nat) := fun y0 : nat => (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0)).
Definition term136 (x0 : type1002) (x1 : Prop) := exists y0 : nat -> nat, (x0 y0) /\ x1.
Definition term223 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0)).
Definition term457 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.le (S x0) x1)) \/ (Peano.lt x0 x1)).
Definition term286 (x0 : nat -> nat) (x1 : nat -> Prop) := fun y0 : nat => exists y1 : nat -> nat, ((forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (@IN nat y2 x1)))) \/ ((forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))).
Definition term68 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term291 (x0 : nat) := fun y0 : nat => ((Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) /\ ((~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0)).
Definition term227 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term421 (x0 : nat) (x1 : nat -> Prop) := imp (@IN nat x0 x1).
Definition term437 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (x0 x1) x1)) -> Peano.le (x0 x1) x1.
Definition term167 (x0 : nat -> nat) (x1 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1))).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (~ (Peano.le x0 x1)) \/ (~ (@IN nat x1 x2)).
Definition term419 (x0 : nat) (x1 : nat -> Prop) := ~ (~ (@IN nat x0 x1)).
Definition term193 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term407 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (@IN nat y0 x1))) x2.
Definition term353 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.lt x0 x1).
Definition term240 (x0 : nat -> nat) (x1 : nat -> Prop) := ((fun y0 : nat -> nat => exists y1 : nat, (forall y2 : nat, (@IN nat (y0 y2) x1) /\ (~ (Peano.le (y0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1)))) x0) \/ (exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))).
Definition term91 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => exists y2 : nat, (Peano.le y1 y2) /\ (@IN nat y2 x0)) y0).
Definition term72 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (@IN nat y2 x0) -> Peano.le y2 y1) y0).
Definition term177 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (Peano.le y1 y2) /\ (@IN nat y2 x0)) x1 y0.
Definition term117 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (@IN nat y2 x0) /\ (~ (Peano.le y2 y1))) x1 y0.
Definition term230 (x0 : nat -> Prop) := (exists y0 : nat -> nat, (fun y1 : nat -> nat => exists y2 : nat, (forall y3 : nat, (@IN nat (y1 y3) x0) /\ (~ (Peano.le (y1 y3) y3))) /\ (forall y3 : nat, (~ (Peano.le y2 y3)) \/ (~ (@IN nat y3 x0)))) y0) \/ (exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0))).
Definition term369 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1) /\ ((fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1).
Definition term309 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) x1) /\ ((fun y0 : nat => (~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0)) x1).
Definition term298 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term470 (x0 : nat) (x1 : nat) := ~ ((Peano.le x1 x0) /\ (Peano.lt x0 x1)).
Definition term255 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0))) x1.
Definition term253 (x0 : nat -> nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1)))) y0.
Definition term163 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := (forall y0 : nat, (@IN nat (x0 y0) x1) /\ (~ (Peano.le (x0 y0) y0))) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1))) x2).
Definition term416 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (~ (@IN nat x2 x0))) -> ~ (Peano.le x1 x2).
Definition term202 (x0 : nat -> Prop) (x1 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) x1).
Definition term212 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat -> nat, (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 x0)) /\ ((fun y1 : nat -> nat => forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1)) y0).
Definition term13 (x0 : nat -> Prop) := ((~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term435 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.lt x1 (x0 x1))) -> Peano.le (x0 x1) x1.
Definition term85 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (@IN nat y0 x1)).
Definition term409 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (Peano.le y0 (x0 y0)) /\ (@IN nat (x0 y0) x1)) x2.
Definition term381 (x0 : nat) := (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ (forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term321 (x0 : nat) := (forall y0 : nat, (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) /\ (forall y0 : nat, (~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0)).
Definition term219 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> Prop) := (forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ (forall y0 : nat, (Peano.le y0 (x1 y0)) /\ (@IN nat (x1 y0) x2)).
Definition term164 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := (forall y0 : nat, (@IN nat (x0 y0) x2) /\ (~ (Peano.le (x0 y0) y0))) /\ (forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (@IN nat y0 x2))).
Definition term275 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat -> nat, ((forall y1 : nat, (@IN nat (x0 y1) x2) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le x1 y1)) \/ (~ (@IN nat y1 x2)))) \/ ((fun y1 : nat -> nat => (forall y2 : nat, (~ (@IN nat y2 x2)) \/ (Peano.le y2 x1)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x2))) y0).
Definition term454 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (S x1) (x0 (S x1))).
Definition term456 (x0 : nat) (x1 : nat) := ~ (Peano.le (S x0) x1).
Definition term466 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.lt x1 (x0 (S x1)))) -> Peano.lt x1 (x0 (S x1)).
Definition term25 (x0 : nat -> Prop) := imp (~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))).
Definition term288 (x0 : nat -> Prop) := fun y0 : nat -> nat => exists y1 : nat, exists y2 : nat -> nat, ((forall y3 : nat, (@IN nat (y0 y3) x0) /\ (~ (Peano.le (y0 y3) y3))) /\ (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (@IN nat y3 x0)))) \/ ((forall y3 : nat, (~ (@IN nat y3 x0)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x0))).
Definition term173 (x0 : nat -> Prop) := fun y0 : nat => fun y1 : nat => (Peano.le y0 y1) /\ (@IN nat y1 x0).
Definition term399 := and (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))).
Definition term339 := and (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))).
Definition term99 (x0 : nat -> Prop) := and (forall y0 : nat, exists y1 : nat, (@IN nat y1 x0) /\ (~ (Peano.le y1 y0))).
Definition term264 (x0 : nat -> nat) (x1 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1)))) y0) \/ ((fun y1 : nat => exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x1)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x1))) y0).
Definition term410 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 x1) x1).
Definition term429 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term192 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term135 (x0 : type1002) (x1 : Prop) := (exists y0 : nat -> nat, x0 y0) /\ x1.
Definition term11 (x0 : nat -> Prop) := ~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0))).
Definition term138 (x0 : nat -> Prop) := exists y0 : nat -> nat, ((fun y1 : nat -> nat => forall y2 : nat, (@IN nat (y1 y2) x0) /\ (~ (Peano.le (y1 y2) y2))) y0) /\ (exists y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0))).
Definition term476 := forall y0 : nat -> Prop, (@INFINITE nat y0) = (forall y1 : nat, exists y2 : nat, (Peano.le y1 y2) /\ (@IN nat y2 y0)).
Definition term266 (x0 : nat -> nat) (x1 : nat -> Prop) := exists y0 : nat, ((forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) \/ (exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))).
Definition term81 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => (Peano.le x0 y1) /\ (@IN nat y1 x1)) y0).
Definition term69 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (@IN nat y2 x0) -> Peano.le y2 y1) y0).
Definition term400 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term395 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term340 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0.
Definition term335 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0.
Definition term197 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0.
Definition term159 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0))) y0.
Definition term444 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((~ (@IN nat x1 x0)) \/ (Peano.le x1 x2)).
Definition term404 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.le y0 y1)) x0.
Definition term390 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0.
Definition term388 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0.
Definition term330 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)) x0.
Definition term328 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) x0.
Definition term102 (x0 : nat -> Prop) := or ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) /\ (~ (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))).
Definition term186 (x0 : nat -> Prop) (x1 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (Peano.le y1 y2) /\ (@IN nat y2 x0)) y0 (x1 y0).
Definition term126 (x0 : nat -> Prop) (x1 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (@IN nat y2 x0) /\ (~ (Peano.le y2 y1))) y0 (x1 y0).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ~ ((Peano.le x0 x1) /\ (@IN nat x1 x2)).
Definition term262 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := ((fun y0 : nat => (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) x2) \/ ((fun y0 : nat => exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))) x2).
Definition term349 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term445 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((Peano.le x1 x0) \/ (~ (@IN nat x1 x2))).
Definition term283 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat -> nat => ((forall y1 : nat, (@IN nat (x0 y1) x2) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le x1 y1)) \/ (~ (@IN nat y1 x2)))) \/ ((fun y1 : nat -> nat => (forall y2 : nat, (~ (@IN nat y2 x2)) \/ (Peano.le y2 x1)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x2))) y0).
Definition term263 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := ((forall y0 : nat, (@IN nat (x0 y0) x2) /\ (~ (Peano.le (x0 y0) y0))) /\ (forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (@IN nat y0 x2)))) \/ (exists y0 : nat -> nat, (forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x1)) /\ (forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x2))).
Definition term60 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 x0) -> Peano.le y0 x1) x2.
Definition term235 (x0 : nat -> Prop) := or (exists y0 : nat -> nat, (fun y1 : nat -> nat => exists y2 : nat, (forall y3 : nat, (@IN nat (y1 y3) x0) /\ (~ (Peano.le (y1 y3) y3))) /\ (forall y3 : nat, (~ (Peano.le y2 y3)) \/ (~ (@IN nat y3 x0)))) y0).
Definition term132 (x0 : nat -> Prop) := (exists y0 : nat -> nat, forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))) /\ (exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x0))).
Definition term344 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) \/ (Peano.le x0 x1).
Definition term364 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term375 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term86 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (@IN nat y0 x1)).
Definition term233 (x0 : nat -> Prop) := fun y0 : nat -> nat => (fun y1 : nat -> nat => exists y2 : nat, (forall y3 : nat, (@IN nat (y1 y3) x0) /\ (~ (Peano.le (y1 y3) y3))) /\ (forall y3 : nat, (~ (Peano.le y2 y3)) \/ (~ (@IN nat y3 x0)))) y0.
Definition term5 (x0 : nat -> Prop) := ~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0).
Definition term122 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 x0) /\ (~ (Peano.le y0 x2))) (x1 x2).
Definition term65 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1).
Definition term88 (x0 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => exists y2 : nat, (Peano.le y1 y2) /\ (@IN nat y2 x0)) y0).
Definition term59 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (@IN nat y1 x0) -> Peano.le y1 x1) y0).
Definition term40 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term231 (x0 : nat -> Prop) := exists y0 : nat -> nat, ((fun y1 : nat -> nat => exists y2 : nat, (forall y3 : nat, (@IN nat (y1 y3) x0) /\ (~ (Peano.le (y1 y3) y3))) /\ (forall y3 : nat, (~ (Peano.le y2 y3)) \/ (~ (@IN nat y3 x0)))) y0) \/ (exists y1 : nat, exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x0)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x0))).
Definition term260 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := or ((fun y0 : nat => (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) x2).
Definition term225 (x0 : nat -> Prop) := (exists y0 : nat -> nat, exists y1 : nat, (forall y2 : nat, (@IN nat (y0 y2) x0) /\ (~ (Peano.le (y0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0)))) \/ (exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0))).
Definition term178 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.le y2 y3) /\ (@IN nat y3 x0)) y0 y1.
Definition term118 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (@IN nat y3 x0) /\ (~ (Peano.le y3 y2))) y0 y1.
Definition term411 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat (x0 x1) x2.
Definition term378 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term318 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0.
Definition term150 (x0 : nat -> Prop) := fun y0 : nat -> nat => (forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))) /\ (exists y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0))).
Definition term21 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term438 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 x1) x1) -> False.
Definition term148 (x0 : nat -> nat) (x1 : nat -> Prop) := (forall y0 : nat, (@IN nat (x0 y0) x1) /\ (~ (Peano.le (x0 y0) y0))) /\ (exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1))).
Definition term398 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0).
Definition term376 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0).
Definition term338 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0).
Definition term316 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0).
Definition term389 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0).
Definition term329 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) x0).
Definition term206 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0) /\ (exists y1 : nat -> nat, forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0)).
Definition term174 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (Peano.le y0 y1) /\ (@IN nat y1 x0)) x1.
Definition term182 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (Peano.le x2 y0) /\ (@IN nat y0 x0)) (x1 x2).
Definition term406 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (@IN nat (x1 y0) x0) /\ (~ (Peano.le (x1 y0) y0))) x2.
Definition term461 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le (S x0) x1))).
Definition term431 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.lt x1 (x0 x1)).
Definition term448 (x0 : nat -> nat) (x1 : nat) := x0 (S x1).
Definition term350 (x0 : nat) (x1 : nat) := or (~ (~ (Peano.le x0 x1))).
Definition term462 (x0 : nat) (x1 : nat) := imp (Peano.le (S x0) x1).
Definition term265 (x0 : nat -> nat) (x1 : nat -> Prop) := fun y0 : nat => ((forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) \/ (exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))).
Definition term386 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term326 := fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1)).
Definition term92 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x0)).
Definition term217 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((forall y0 : nat, (~ (@IN nat y0 x1)) \/ (Peano.le y0 x0)) /\ (exists y0 : nat -> nat, forall y1 : nat, (Peano.le y1 (y0 y1)) /\ (@IN nat (y0 y1) x1))).
Definition term216 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((forall y0 : nat, (~ (@IN nat y0 x1)) \/ (Peano.le y0 x0)) /\ (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1)) y0)).
Definition term162 (x0 : nat -> nat) (x1 : nat -> Prop) := @eq Prop ((forall y0 : nat, (@IN nat (x0 y0) x1) /\ (~ (Peano.le (x0 y0) y0))) /\ (exists y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))).
Definition term161 (x0 : nat -> nat) (x1 : nat -> Prop) := @eq Prop ((forall y0 : nat, (@IN nat (x0 y0) x1) /\ (~ (Peano.le (x0 y0) y0))) /\ (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1))) y0)).
Definition term295 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term257 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x0)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x0))) y0.
Definition term198 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0.
Definition term160 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0))) y0.
Definition term287 (x0 : nat -> nat) (x1 : nat -> Prop) := exists y0 : nat, exists y1 : nat -> nat, ((forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (@IN nat y2 x1)))) \/ ((forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1))).
Definition term224 (x0 : nat -> Prop) := exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0)).
Definition term383 := forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term323 := forall y0 : nat, (forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)).
Definition term229 (x0 : type1002) (x1 : Prop) := exists y0 : nat -> nat, (x0 y0) \/ x1.
Definition term248 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term452 (x0 : nat -> nat) (x1 : nat) := Peano.le (S x1) (x0 (S x1)).
Definition term465 (x0 : nat -> nat) (x1 : nat) := Peano.lt x1 (x0 (S x1)).
Definition term473 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 (S x1)) x1) /\ (Peano.lt x1 (x0 (S x1))).
Definition term367 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1).
Definition term305 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) x1).
Definition term84 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.le x0 y1) /\ (@IN nat y1 x1)) y0).
Definition term62 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (@IN nat y1 x0) -> Peano.le y1 x1) y0).
Definition term35 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> Peano.le x0 x1.
Definition term145 (x0 : nat -> Prop) (x1 : nat -> nat) := and ((fun y0 : nat -> nat => forall y1 : nat, (@IN nat (y0 y1) x0) /\ (~ (Peano.le (y0 y1) y1))) x1).
Definition term356 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((Peano.le x1 x0) \/ (Peano.lt x0 x1)).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term37 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> Peano.le x0 y0.
Definition term10 (x0 : nat -> Prop) := (~ ((~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)) = (forall y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (@IN nat y1 x0)))) -> False.
Definition term254 (x0 : nat -> nat) (x1 : nat -> Prop) := or (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1)))) y0).
Definition term41 (x0 : nat) := fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term346 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (Peano.le x0 y0).
Definition term320 (x0 : nat) := forall y0 : nat, (~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0).
Definition term30 := forall y0 : nat -> Prop, (~ ((~ (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) = (forall y1 : nat, exists y2 : nat, (Peano.le y1 y2) /\ (@IN nat y2 y0)))) -> (forall y1 : nat, forall y2 : nat, (Peano.le (S y1) y2) = (Peano.lt y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)).
Definition term29 := forall y0 : nat -> Prop, (~ ((~ (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1)) = (forall y1 : nat, exists y2 : nat, (Peano.le y1 y2) /\ (@IN nat y2 y0)))) -> (forall y1 : nat, forall y2 : nat, (Peano.le (S y1) y2) = (Peano.lt y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False.
Definition term55 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (@IN nat x1 x0)) \/ (Peano.le x1 x2).
Definition term77 (x0 : nat -> Prop) := ~ (~ (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0)).
Definition term459 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le (S x0) x1))) -> Peano.lt x0 x1.
Definition term401 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term396 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term341 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0.
Definition term336 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0.
Definition term107 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term22 := imp (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)).
Definition term19 := imp (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@INFINITE a0 y0) = (~ (@FINITE a0 y0))) x0.
Definition term53 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ ((@IN nat x1 x0) -> Peano.le x1 x2).
Definition term63 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (@IN nat y0 x0) /\ (~ (Peano.le y0 x1)).
Definition term220 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat -> nat => (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 x0)) /\ ((fun y1 : nat -> nat => forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1)) y0).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term156 (x0 : nat -> nat) (x1 : nat -> Prop) := (forall y0 : nat, (@IN nat (x0 y0) x1) /\ (~ (Peano.le (x0 y0) y0))) /\ (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1))) y0).
Definition term57 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term464 (x0 : nat -> nat) (x1 : nat) := (Peano.le (S x1) (x0 (S x1))) -> Peano.lt x1 (x0 (S x1)).
Definition term80 (x0 : nat) (x1 : nat -> Prop) := ~ (exists y0 : nat, (Peano.le x0 y0) /\ (@IN nat y0 x1)).
Definition term365 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1.
Definition term359 := fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term293 := fun y0 : nat => forall y1 : nat, ((Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ ((~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)).
Definition term247 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term427 (x0 : Prop) := x0 -> ~ x0.
Definition term54 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x1 x0) /\ (~ (Peano.le x1 x2)).
Definition term290 (x0 : nat) (x1 : nat) := ((Peano.le (S x0) x1) \/ (~ (Peano.lt x0 x1))) /\ ((~ (Peano.le (S x0) x1)) \/ (Peano.lt x0 x1)).
Definition term420 (x0 : nat) (x1 : nat -> Prop) := imp (~ (~ (@IN nat x0 x1))).
Definition term157 (x0 : nat -> nat) (x1 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1))) y0).
Definition term446 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (~ (@IN nat x1 x0))) -> Peano.le x1 x2.
Definition term259 (x0 : nat -> nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (forall y1 : nat, (@IN nat (x0 y1) x1) /\ (~ (Peano.le (x0 y1) y1))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (@IN nat y1 x1)))) \/ (exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x1)))).
Definition term258 (x0 : nat -> nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (@IN nat (x0 y2) x1) /\ (~ (Peano.le (x0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat -> nat, (forall y3 : nat, (~ (@IN nat y3 x1)) \/ (Peano.le y3 y1)) /\ (forall y3 : nat, (Peano.le y3 (y2 y3)) /\ (@IN nat (y2 y3) x1))) y0)).
Definition term237 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat -> nat, exists y1 : nat, (forall y2 : nat, (@IN nat (y0 y2) x0) /\ (~ (Peano.le (y0 y2) y2))) /\ (forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (@IN nat y2 x0)))) \/ (exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0)))).
Definition term236 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat -> nat, (fun y1 : nat -> nat => exists y2 : nat, (forall y3 : nat, (@IN nat (y1 y3) x0) /\ (~ (Peano.le (y1 y3) y3))) /\ (forall y3 : nat, (~ (Peano.le y2 y3)) \/ (~ (@IN nat y3 x0)))) y0) \/ (exists y0 : nat, exists y1 : nat -> nat, (forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y0)) /\ (forall y2 : nat, (Peano.le y2 (y1 y2)) /\ (@IN nat (y1 y2) x0)))).
