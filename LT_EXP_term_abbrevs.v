Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term245 := Peano.lt (NUMERAL (BIT1 0)).
Definition term437 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 (Nat.mul x0 x0)).
Definition term284 (x0 : nat) (x1 : nat) (x2 : nat) := ((x1 = (NUMERAL (BIT1 0))) \/ (Peano.le x0 x2)) -> Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term279 (x0 : nat) (x1 : nat) (x2 : nat) := (((x1 = (S (NUMERAL 0))) \/ (x1 = (NUMERAL 0))) \/ (Peano.le x0 x2)) -> Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term267 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x1 (NUMERAL (BIT0 (BIT1 0)))) \/ (Peano.le x0 x2)) -> Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term355 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 y0)) (Nat.add x1 (S x2)).
Definition term292 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (Nat.pow x1 x0) (Nat.pow x1 y0)) x2.
Definition term81 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.lt x0 y0) /\ (Peano.le y0 x1).
Definition term36 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term230 (x0 : nat) := ((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) x0) -> (fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) (S x0).
Definition term285 (x0 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) x0.
Definition term339 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term322 (x0 : nat) (x1 : nat) := Nat.pow x0 (Nat.add x1 (NUMERAL 0)).
Definition term109 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term372 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) -> Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (S y0)))).
Definition term151 (x0 : nat) (x1 : nat) := or ((Peano.le (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0)) /\ (Peano.lt x0 x1)).
Definition term286 (x0 : nat) := Nat.pow (NUMERAL (BIT1 0)) x0.
Definition term221 := Peano.lt (Nat.pow (NUMERAL 0) (NUMERAL 0)) (NUMERAL (BIT1 0)).
Definition term125 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (Peano.le x1 x2).
Definition term203 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) y0.
Definition term386 (x0 : nat) (x1 : nat) := Peano.lt (Nat.pow x0 x1) (Nat.mul x0 (Nat.pow x0 x1)).
Definition term431 (x0 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 (Nat.mul x0 x0))) -> Peano.le x0 (Nat.mul x0 x0).
Definition term152 := @eq nat (NUMERAL 0).
Definition term22 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term116 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term318 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) y0.
Definition term344 (x0 : Prop) := ~ (~ x0).
Definition term73 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) x0.
Definition term51 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2)) x0.
Definition term44 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y2) (Nat.mul y1 y2)) = ((Peano.le y0 y1) \/ (y2 = (NUMERAL 0)))) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term237 := ((Peano.lt (Nat.pow (NUMERAL 0) (NUMERAL 0)) (NUMERAL (BIT1 0))) = (~ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) (S y0)) (NUMERAL (BIT1 0))) = (~ ((S y0) = (NUMERAL 0)))).
Definition term421 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Peano.lt (Nat.pow x0 x1) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2)))))) -> Peano.lt (Nat.pow x0 x1) (Nat.mul x0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2)))).
Definition term359 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0))).
Definition term186 (x0 : nat) := and ((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (NUMERAL 0))) = ((~ (x0 = (NUMERAL 0))) /\ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term189 (x0 : nat) (x1 : nat) := imp ((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) x1)) = ((~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0)))).
Definition term215 (x0 : nat) := Peano.lt (Nat.pow (NUMERAL 0) x0) (NUMERAL 0).
Definition term181 (x0 : nat) := fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0))).
Definition term352 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term86 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1.
Definition term41 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2))).
Definition term210 (x0 : nat) := @eq Prop (Peano.lt (Nat.pow (NUMERAL 0) x0) (NUMERAL (BIT1 0))).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term248 (x0 : nat) := Peano.lt (Nat.pow (NUMERAL 0) (S x0)).
Definition term240 := fun y0 : nat => (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) y0.
Definition term165 := S (NUMERAL 0).
Definition term214 (x0 : nat) := Nat.mul (NUMERAL 0) (Nat.pow (NUMERAL 0) x0).
Definition term60 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term196 (x0 : nat) := fun y0 : nat => ((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (S y0))) = ((~ (x0 = (NUMERAL 0))) /\ ((S y0) = (NUMERAL 0))).
Definition term137 (x0 : nat) (x1 : nat) := Peano.lt (Nat.pow x0 x1).
Definition term65 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term332 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (NUMERAL (BIT1 0)) (Nat.pow x0 (Nat.add x1 x2)).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term117 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term302 (x0 : nat) (x1 : nat) := and (Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (NUMERAL 0)))).
Definition term136 (x0 : nat) := Nat.pow (NUMERAL 0) x0.
Definition term380 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) y0.
Definition term319 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) y0.
Definition term241 := forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) y0.
Definition term204 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) y0.
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0)) x2.
Definition term423 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 (Nat.add x1 (S x2))) (Nat.mul x0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2)))).
Definition term35 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term166 := S (S (NUMERAL 0)).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0)))) x2.
Definition term375 (x0 : nat) (x1 : nat) := ((fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) y0) -> (fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) (S y0)).
Definition term314 (x0 : nat) (x1 : nat) := ((fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) y0) -> (fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) (S y0)).
Definition term236 := ((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) (S y0)).
Definition term199 (x0 : nat) := ((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) (S y0)).
Definition term97 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term93 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1))).
Definition term422 (x0 : nat) (x1 : nat) (x2 : nat) := and (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S x2)))).
Definition term363 (x0 : nat) (x1 : nat) := and (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (NUMERAL 0))))).
Definition term178 (x0 : nat) (x1 : nat) := False \/ ((~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0))).
Definition term271 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.lt x0 (NUMERAL 0)).
Definition term400 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0)).
Definition term168 := Peano.lt (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term84 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.lt x0 y1) /\ (Peano.le y1 y0)) -> Peano.lt x0 y0.
Definition term39 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term261 (x0 : nat) := or (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term190 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) (S x1).
Definition term340 (x0 : nat) := ~ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term258 (x0 : nat) := ~ (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term278 (x0 : nat) (x1 : nat) (x2 : nat) := imp (((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))) \/ (Peano.le x1 x2)).
Definition term90 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term102 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term298 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0)).
Definition term62 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term255 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term193 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) x1) -> (fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) (S x1).
Definition term103 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term153 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term358 (x0 : nat) (x1 : nat) := (((fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) y0) -> (fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) y0.
Definition term297 (x0 : nat) (x1 : nat) := (((fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) y0) -> (fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) y0.
Definition term218 := (((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) y0.
Definition term180 (x0 : nat) := (((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) y0.
Definition term227 (x0 : nat) := imp ((Peano.lt (Nat.pow (NUMERAL 0) x0) (NUMERAL (BIT1 0))) = (~ (x0 = (NUMERAL 0)))).
Definition term61 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term6 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term121 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term179 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term334 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 x1) (Nat.mul (NUMERAL (BIT1 0)) (Nat.pow x0 (Nat.add x1 x2))).
Definition term249 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term343 (x0 : nat) := imp (Peano.lt x0 (NUMERAL (BIT1 0))).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term100 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term254 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term377 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) y0) -> (fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) (S y0))).
Definition term316 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) y0) -> (fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) (S y0))).
Definition term238 := imp (((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) (S y0))).
Definition term201 (x0 : nat) := imp (((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) (S y0))).
Definition term402 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (Nat.add x0 y0)) = (Peano.lt (NUMERAL 0) y0).
Definition term54 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term140 (x0 : nat) (x1 : nat) := Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) x1).
Definition term143 := Peano.le (NUMERAL (BIT0 (BIT1 0))).
Definition term147 := and (Peano.le (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0)).
Definition term101 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term91 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term399 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL 0) (Nat.pow x0 x1).
Definition term408 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.pow x0 x1).
Definition term207 := Nat.pow (NUMERAL 0) (NUMERAL 0).
Definition term161 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2)) \/ False.
Definition term351 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.pow x0 x1) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2)))).
Definition term222 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term415 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) \/ ((Nat.pow x0 x1) = (NUMERAL 0)).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.lt (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term444 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 y0)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 y0)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0))))).
Definition term397 (x0 : nat) := forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.pow y0 x0)) = ((~ (y0 = (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term205 (x0 : nat) := forall y0 : nat, (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0))).
Definition term47 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0))).
Definition term75 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1) x1.
Definition term53 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1)) x1.
Definition term46 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0)))) x1.
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term320 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0)).
Definition term373 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) y0) -> (fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) (S y0).
Definition term312 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) y0) -> (fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) (S y0).
Definition term234 := forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) (S y0).
Definition term197 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) (S y0).
Definition term135 := Nat.pow (NUMERAL 0).
Definition term134 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term126 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term5 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term348 (x0 : nat) := (x0 = (NUMERAL 0)) -> x0 = (NUMERAL 0).
Definition term251 := @eq Prop (Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term299 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) (NUMERAL 0).
Definition term156 (x0 : nat) (x1 : nat) := True /\ ((~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0))).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2).
Definition term233 := fun y0 : nat => ((Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) (S y0)) (NUMERAL (BIT1 0))) = (~ ((S y0) = (NUMERAL 0))).
Definition term281 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ False.
Definition term440 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.lt (Nat.pow x0 x1) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))))).
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))) \/ (Peano.le x1 x2).
Definition term347 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term89 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term24 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term333 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 x2).
Definition term260 (x0 : nat) := or (~ (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term311 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) -> Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0))).
Definition term138 (x0 : nat) := Peano.lt (Nat.pow (NUMERAL 0) x0).
Definition term20 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term362 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) (NUMERAL 0)).
Definition term301 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) (NUMERAL 0)).
Definition term223 := and ((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) (NUMERAL 0)).
Definition term185 (x0 : nat) := and ((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0)).
Definition term12 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term433 (x0 : nat) := Peano.le (Nat.mul x0 (NUMERAL (BIT1 0))) (Nat.mul x0 x0).
Definition term162 := ~ (Peano.lt (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term242 := forall y0 : nat, (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0))).
Definition term280 (x0 : nat) := or (x0 = (NUMERAL (BIT1 0))).
Definition term407 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term435 (x0 : nat) := (Peano.le x0 (Nat.mul x0 (NUMERAL (BIT1 0)))) /\ (Peano.le (Nat.mul x0 (NUMERAL (BIT1 0))) (Nat.mul x0 x0)).
Definition term194 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) x1)) = ((~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (S x1))) = ((~ (x0 = (NUMERAL 0))) /\ ((S x1) = (NUMERAL 0))).
Definition term367 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) (S x2).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0) x2.
Definition term426 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 (Nat.add x1 (S x2))).
Definition term356 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S x2))).
Definition term7 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term123 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term398 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.pow y0 x0)) = ((~ (y0 = (NUMERAL 0))) \/ (x0 = (NUMERAL 0)))) x1.
Definition term83 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.lt x0 y0) /\ (Peano.le y0 x1)) -> Peano.lt x0 x1.
Definition term349 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.pow x0 x1) (Nat.mul (NUMERAL (BIT1 0)) (Nat.pow x0 (Nat.add x1 x2)))) /\ (Peano.le (Nat.mul (NUMERAL (BIT1 0)) (Nat.pow x0 (Nat.add x1 x2))) (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2)))).
Definition term174 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term171 := Peano.lt (NUMERAL 0) (S (NUMERAL 0)).
Definition term428 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x0) (Nat.pow x0 (Nat.add x1 x2)).
Definition term438 (x0 : nat) := Peano.le x0 (Nat.mul x0 x0).
Definition term120 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term371 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) y0) -> (fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) (S y0).
Definition term310 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) y0) -> (fun y1 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y1))) (S y0).
Definition term232 := fun y0 : nat => ((fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y1) (NUMERAL (BIT1 0))) = (~ (y1 = (NUMERAL 0)))) (S y0).
Definition term195 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) y0) -> (fun y1 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y1)) = ((~ (x0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))) (S y0).
Definition term183 (x0 : nat) := Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (NUMERAL 0)).
Definition term300 (x0 : nat) (x1 : nat) := Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (NUMERAL 0))).
Definition term187 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) x1.
Definition term99 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term406 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) x0.
Definition term429 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))) (Nat.mul (Nat.mul x0 x0) (Nat.pow x0 (Nat.add x1 x2))).
Definition term71 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term112 (x0 : nat) := (~ (Peano.lt x0 x0)) -> (Peano.lt x0 x0) = False.
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term287 := Nat.pow (NUMERAL (BIT1 0)).
Definition term368 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (S x2)))).
Definition term361 (x0 : nat) (x1 : nat) := Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (NUMERAL 0)))).
Definition term282 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2).
Definition term272 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term336 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) \/ ((Nat.pow x0 (Nat.add x1 x2)) = (NUMERAL 0)).
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0))).
Definition term390 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 (S (S x2))).
Definition term446 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.pow y0 y1) (Nat.pow y0 y2)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) y0) /\ (Peano.lt y1 y2)) \/ ((y0 = (NUMERAL 0)) /\ ((~ (y1 = (NUMERAL 0))) /\ (y2 = (NUMERAL 0))))).
Definition term445 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.pow x0 y0) (Nat.pow x0 y1)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt y0 y1)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (y0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0))))).
Definition term129 := forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term128 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term85 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1.
Definition term74 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1.
Definition term72 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term66 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term58 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term52 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term45 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0))).
Definition term40 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term29 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term27 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term14 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term175 := or ((NUMERAL 0) = (S (NUMERAL 0))).
Definition term268 (x0 : nat) := Peano.lt x0 (S (S (NUMERAL 0))).
Definition term324 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 (S x2)).
Definition term133 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term403 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (Nat.add x0 y0)) = (Peano.lt (NUMERAL 0) y0)) x1.
Definition term293 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 y0)) (Nat.add x1 x2).
Definition term149 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0)) /\ (Peano.lt x0 x1).
Definition term224 := and ((Peano.lt (Nat.pow (NUMERAL 0) (NUMERAL 0)) (NUMERAL (BIT1 0))) = (~ ((NUMERAL 0) = (NUMERAL 0)))).
Definition term105 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term10 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term244 := Peano.lt (Nat.pow (NUMERAL 0) (NUMERAL 0)).
Definition term283 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2)).
Definition term264 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (Peano.le x1 x2)).
Definition term167 := Peano.lt (NUMERAL 0).
Definition term269 (x0 : nat) := (x0 = (S (NUMERAL 0))) \/ (Peano.lt x0 (S (NUMERAL 0))).
Definition term383 (x0 : nat) := Nat.add x0 (S (NUMERAL 0)).
Definition term416 (x0 : nat) := or (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term176 := ((NUMERAL 0) = (S (NUMERAL 0))) \/ True.
Definition term436 (x0 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 (Nat.mul x0 x0)).
Definition term4 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term391 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (S (S (Nat.add x1 x2))).
Definition term164 := S (NUMERAL (BIT1 0)).
Definition term208 (x0 : nat) := Peano.lt (Nat.pow (NUMERAL 0) x0) (NUMERAL (BIT1 0)).
Definition term382 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (NUMERAL 0))))) /\ (forall y0 : nat, (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) -> Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (S y0)))))) -> forall y0 : nat, Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0))).
Definition term321 (x0 : nat) (x1 : nat) := ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (NUMERAL 0)))) /\ (forall y0 : nat, (Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) -> Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0))))) -> forall y0 : nat, Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0)).
Definition term206 (x0 : nat) := (((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (NUMERAL 0))) = ((~ (x0 = (NUMERAL 0))) /\ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (S y0))) = ((~ (x0 = (NUMERAL 0))) /\ ((S y0) = (NUMERAL 0))))) -> forall y0 : nat, (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0))).
Definition term353 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.lt (Nat.pow x1 x0) (Nat.pow x1 y0).
Definition term329 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term434 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term63 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term188 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) x1).
Definition term330 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term124 (x0 : nat) := fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term410 (x0 : nat) (x1 : nat) := Peano.lt (Nat.pow x0 x1) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.pow x0 x1)).
Definition term338 (x0 : nat) := (~ (Peano.le (NUMERAL (BIT1 0)) x0)) -> ~ (~ (x0 = (NUMERAL 0))).
Definition term443 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt (Nat.pow x1 x0) (Nat.pow x1 x2)) -> (Peano.le (NUMERAL (BIT0 (BIT1 0))) x1) /\ (Peano.lt x0 x2)) /\ (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x1) /\ (Peano.lt x0 x2)) -> Peano.lt (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term393 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))).
Definition term111 (x0 : nat) := ~ (Peano.lt x0 x0).
Definition term16 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term2 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term326 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2)).
Definition term412 (x0 : nat) := or (~ (x0 = (NUMERAL 0))).
Definition term247 := @eq Prop (Peano.lt (Nat.pow (NUMERAL 0) (NUMERAL 0)) (NUMERAL (BIT1 0))).
Definition term360 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) (NUMERAL 0).
Definition term114 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term430 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 (Nat.mul x0 x0)) \/ ((Nat.pow x0 (Nat.add x1 x2)) = (NUMERAL 0)).
Definition term146 (x0 : nat) := and (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term341 (x0 : nat) := Peano.lt x0 (NUMERAL (BIT1 0)).
Definition term306 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) (S x2).
Definition term411 (x0 : nat) (x1 : nat) := Peano.lt (Nat.pow x0 x1) (Nat.add (Nat.pow x0 x1) (Nat.pow x0 x1)).
Definition term252 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 x2)) -> (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2).
Definition term95 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 (S y0)).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term327 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 x1) (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))).
Definition term381 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0))).
Definition term274 (x0 : nat) := or (x0 = (S (NUMERAL 0))).
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term177 (x0 : nat) (x1 : nat) := False /\ (Peano.lt x0 x1).
Definition term439 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.lt (Nat.pow x0 x1) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))))).
Definition term419 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.lt (Nat.pow x0 x1) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.pow x0 x1))).
Definition term350 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.le (Nat.pow x0 x1) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2)))).
Definition term64 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term23 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term163 := NUMERAL (BIT0 (BIT1 0)).
Definition term76 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0.
Definition term31 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term370 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S x2)))) -> Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (S x2)))).
Definition term275 (x0 : nat) := (x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0)).
Definition term211 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term270 (x0 : nat) := Peano.lt x0 (S (NUMERAL 0)).
Definition term342 (x0 : nat) := imp (~ (Peano.le (NUMERAL (BIT1 0)) x0)).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (Peano.le x1 x2).
Definition term246 := Peano.lt (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term80 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> Peano.lt x0 x1.
Definition term172 := ((NUMERAL 0) = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term8 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term294 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 x2)).
Definition term107 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term409 (x0 : nat) (x1 : nat) := Nat.add (Nat.pow x0 x1) (Nat.pow x0 x1).
Definition term169 := Peano.lt (NUMERAL 0) (S (S (NUMERAL 0))).
Definition term366 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S x2)))).
Definition term387 (x0 : nat) (x1 : nat) := Nat.add x0 (S (S x1)).
Definition term26 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term184 (x0 : nat) := (~ (x0 = (NUMERAL 0))) /\ ((NUMERAL 0) = (NUMERAL 0)).
Definition term216 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (S x1))).
Definition term217 (x0 : nat) := (~ (x0 = (NUMERAL 0))) /\ False.
Definition term307 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S x2))).
Definition term388 (x0 : nat) (x1 : nat) := S (Nat.add x0 (S x1)).
Definition term257 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0)) \/ (~ (Peano.lt x1 x2)).
Definition term401 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (Nat.add y0 y1)) = (Peano.lt (NUMERAL 0) y1)) x0.
Definition term396 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.pow y1 y0)) = ((~ (y1 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) x0.
Definition term130 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1))) x0.
Definition term104 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) x0.
Definition term96 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term92 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 (S y2)))) x0.
Definition term87 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1) x0.
Definition term67 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term59 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term113 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term154 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0)).
Definition term395 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.lt (Nat.pow x0 x1) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.pow x0 x1)))) -> Peano.lt (Nat.pow x0 x1) (Nat.mul x0 (Nat.pow x0 x1)).
Definition term158 (x0 : nat) (x1 : nat) := ((Peano.le (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0)) /\ (Peano.lt x0 x1)) \/ ((~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0))).
Definition term119 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term413 (x0 : nat) := True \/ (x0 = (NUMERAL 0)).
Definition term250 (x0 : nat) := @eq Prop (Peano.lt (Nat.pow (NUMERAL 0) (S x0)) (NUMERAL (BIT1 0))).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term291 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.pow x1 x0) (Nat.pow x1 y0).
Definition term288 (x0 : nat) (x1 : nat) := Peano.le (Nat.pow x0 x1).
Definition term191 (x0 : nat) (x1 : nat) := Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (S x1)).
Definition term145 := Peano.le (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term144 (x0 : nat) := Peano.le (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term309 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 x2))) -> Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S x2))).
Definition term414 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.pow x0 x1)) (Nat.mul x0 (Nat.pow x0 x1)).
Definition term384 (x0 : nat) := S (Nat.add x0 (NUMERAL 0)).
Definition term219 := fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0))).
Definition term110 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) x0.
Definition term379 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y1)))) y0.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term392 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.pow x0 (S (Nat.add x1 x2))).
Definition term441 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 (S y0)).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x1 x0) /\ (Peano.le x0 x2)) -> Peano.lt x1 x2.
Definition term273 (x0 : nat) := (x0 = (NUMERAL 0)) \/ False.
Definition term70 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term425 (x0 : nat) (x1 : nat) (x2 : nat) := True /\ (Peano.le (Nat.pow x0 (Nat.add x1 (S x2))) (Nat.mul x0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))))).
Definition term131 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0))) x1.
Definition term150 (x0 : nat) (x1 : nat) (x2 : nat) := or ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2)).
Definition term305 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 x2))).
Definition term335 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (NUMERAL (BIT1 0)) (Nat.pow x0 (Nat.add x1 x2))) (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))).
Definition term38 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term427 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))).
Definition term115 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term354 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.lt (Nat.pow x1 x0) (Nat.pow x1 y0)) x2.
Definition term376 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (NUMERAL 0))))) /\ (forall y0 : nat, (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) -> Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (S y0))))).
Definition term424 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S x2)))) /\ (Peano.le (Nat.pow x0 (Nat.add x1 (S x2))) (Nat.mul x0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))))).
Definition term159 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term276 (x0 : nat) := or ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term346 (x0 : nat) := (Peano.lt x0 (NUMERAL (BIT1 0))) -> x0 = (NUMERAL 0).
Definition term213 (x0 : nat) := Nat.pow (NUMERAL 0) (S x0).
Definition term296 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term378 (x0 : nat) (x1 : nat) := imp ((Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (NUMERAL 0))))) /\ (forall y0 : nat, (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) -> Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (S y0)))))).
Definition term317 (x0 : nat) (x1 : nat) := imp ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (NUMERAL 0)))) /\ (forall y0 : nat, (Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) -> Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0))))).
Definition term202 (x0 : nat) := imp (((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (NUMERAL 0))) = ((~ (x0 = (NUMERAL 0))) /\ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (S y0))) = ((~ (x0 = (NUMERAL 0))) /\ ((S y0) = (NUMERAL 0))))).
Definition term404 (x0 : nat) (x1 : nat) := Peano.lt x0 (Nat.add x0 x1).
Definition term420 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt (Nat.pow x0 x1) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.pow x0 x1))).
Definition term212 (x0 : nat) := (~ (x0 = (NUMERAL 0))) /\ True.
Definition term225 (x0 : nat) := (fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) x0.
Definition term253 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x1) /\ (Peano.lt x0 x2))) -> ~ (Peano.lt (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term170 := ((NUMERAL 0) = (S (NUMERAL 0))) \/ (Peano.lt (NUMERAL 0) (S (NUMERAL 0))).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (x2 = (NUMERAL 0)).
Definition term357 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => Peano.lt (Nat.pow x1 x0) (Nat.pow x1 y0)) x2).
Definition term295 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => Peano.le (Nat.pow x1 x0) (Nat.pow x1 y0)) x2).
Definition term265 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.lt (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term82 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt x0 y0) /\ (Peano.le y0 x1).
Definition term37 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term127 := fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term192 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) /\ ((S x1) = (NUMERAL 0)).
Definition term200 (x0 : nat) := ((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (NUMERAL 0))) = ((~ (x0 = (NUMERAL 0))) /\ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (S y0))) = ((~ (x0 = (NUMERAL 0))) /\ ((S y0) = (NUMERAL 0)))).
Definition term256 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2)).
Definition term266 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term160 (x0 : nat) (x1 : nat) := False /\ ((~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0))).
Definition term374 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) -> Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S (S y0)))).
Definition term313 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) -> Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0))).
Definition term198 (x0 : nat) := forall y0 : nat, ((Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (S y0))) = ((~ (x0 = (NUMERAL 0))) /\ ((S y0) = (NUMERAL 0))).
Definition term118 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term385 (x0 : nat) (x1 : nat) := Nat.pow x0 (Nat.add x1 (S (NUMERAL 0))).
Definition term325 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (S (Nat.add x1 x2)).
Definition term369 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) x2) -> (fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) (S x2).
Definition term308 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) x2) -> (fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) (S x2).
Definition term315 (x0 : nat) (x1 : nat) := (Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (NUMERAL 0)))) /\ (forall y0 : nat, (Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) -> Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))).
Definition term182 (x0 : nat) := (fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) y0)) = ((~ (x0 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))) (NUMERAL 0).
Definition term337 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term365 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) x2).
Definition term304 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) x2).
Definition term259 (x0 : nat) := Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term106 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0)) x1.
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term418 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.pow x0 x1) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.pow x0 x1))) /\ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.pow x0 x1)) (Nat.mul x0 (Nat.pow x0 x1))).
Definition term226 (x0 : nat) := imp ((fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) x0).
Definition term345 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term323 (x0 : nat) (x1 : nat) := Peano.le (Nat.pow x0 x1) (Nat.pow x0 x1).
Definition term231 (x0 : nat) := ((Peano.lt (Nat.pow (NUMERAL 0) x0) (NUMERAL (BIT1 0))) = (~ (x0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) (S x0)) (NUMERAL (BIT1 0))) = (~ ((S x0) = (NUMERAL 0))).
Definition term98 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term94 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1)))) x1.
Definition term290 := Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term173 := or ((NUMERAL 0) = (NUMERAL 0)).
Definition term235 := forall y0 : nat, ((Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) (S y0)) (NUMERAL (BIT1 0))) = (~ ((S y0) = (NUMERAL 0))).
Definition term229 (x0 : nat) := Peano.lt (Nat.pow (NUMERAL 0) (S x0)) (NUMERAL (BIT1 0)).
Definition term394 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.pow x0 x1) (Nat.mul x0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2)))).
Definition term21 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term228 (x0 : nat) := (fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) (S x0).
Definition term243 := (((Peano.lt (Nat.pow (NUMERAL 0) (NUMERAL 0)) (NUMERAL (BIT1 0))) = (~ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) (S y0)) (NUMERAL (BIT1 0))) = (~ ((S y0) = (NUMERAL 0))))) -> forall y0 : nat, (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0))).
Definition term142 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) x1)).
Definition term405 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term432 (x0 : nat) := Peano.le x0 (Nat.mul x0 (NUMERAL (BIT1 0))).
Definition term209 (x0 : nat) := @eq Prop (Peano.lt (Nat.pow (NUMERAL 0) x0) (Nat.pow (NUMERAL 0) (NUMERAL 0))).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0)))).
Definition term442 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x1) /\ (Peano.lt x0 x2)) -> Peano.lt (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term364 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.lt (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 (S y0)))) x2.
Definition term303 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 y0))) x2.
Definition term132 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term220 := (fun y0 : nat => (Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) (NUMERAL 0).
Definition term417 (x0 : nat) (x1 : nat) := True \/ ((Nat.pow x0 x1) = (NUMERAL 0)).
Definition term122 := NUMERAL (BIT1 0).
Definition term331 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term289 := Peano.le (NUMERAL (BIT1 0)).
Definition term88 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.lt x0 y1) /\ (Peano.le y1 y0)) -> Peano.lt x0 y0) x1.
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term239 := imp (((Peano.lt (Nat.pow (NUMERAL 0) (NUMERAL 0)) (NUMERAL (BIT1 0))) = (~ ((NUMERAL 0) = (NUMERAL 0)))) /\ (forall y0 : nat, ((Peano.lt (Nat.pow (NUMERAL 0) y0) (NUMERAL (BIT1 0))) = (~ (y0 = (NUMERAL 0)))) -> (Peano.lt (Nat.pow (NUMERAL 0) (S y0)) (NUMERAL (BIT1 0))) = (~ ((S y0) = (NUMERAL 0))))).
Definition term328 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Peano.le (Nat.pow x0 x1) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))))) -> Peano.le (Nat.pow x0 x1) (Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2))).
Definition term108 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (S y0)) x0.
Definition term389 (x0 : nat) (x1 : nat) := S (S (Nat.add x0 x1)).
Definition term68 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
