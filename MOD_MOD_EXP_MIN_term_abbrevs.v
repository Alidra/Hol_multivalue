Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term361 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.pow x1 y0)) (Nat.pow x1 x2)) = (Nat.modulo x0 (Nat.pow x1 x2))) x3).
Definition term276 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 y0)) = (Nat.modulo x0 (Nat.pow x1 x2))) x3).
Definition term525 (x0 : type1606) := fun y0 : nat => (fun y1 : nat => fun y2 : nat -> nat => forall y3 : nat, (~ (Peano.le y1 y3)) \/ (y3 = (Nat.add y1 (y2 y3)))) y0 (x0 y0).
Definition term570 (x0 : type1606) (x1 : nat) (x2 : nat) := ~ (x2 = (Nat.add x1 (x0 x1 x2))).
Definition term92 (x0 : nat) := fun y0 : nat => (Nat.modulo x0 y0) = (Nat.modulo x0 (NUMERAL 0)).
Definition term9 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.lt x0 y0) /\ (Peano.le y0 x1).
Definition term166 (x0 : nat) (x1 : nat) := ((Peano.le x0 (S x1)) \/ (~ ((x0 = (S x1)) \/ (Peano.le x0 x1)))) /\ ((~ (Peano.le x0 (S x1))) \/ ((x0 = (S x1)) \/ (Peano.le x0 x1))).
Definition term257 (x0 : nat) := (~ (~ (Peano.le x0 (NUMERAL 0)))) -> x0 = (NUMERAL 0).
Definition term376 (x0 : nat) (x1 : nat) := (~ (exists y0 : nat, x0 = (Nat.add x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term251 (x0 : nat) := ~ (Peano.le x0 (NUMERAL 0)).
Definition term420 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) /\ ((~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))).
Definition term84 := @COND nat False (NUMERAL (BIT1 0)).
Definition term453 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0).
Definition term232 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0).
Definition term265 := (~ False) -> False.
Definition term261 (x0 : nat) := imp (Peano.le x0 (NUMERAL 0)).
Definition term395 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term72 (x0 : nat) := Nat.modulo (NUMERAL 0) (@COND nat (x0 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term478 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.le x1 x0)) \/ (x0 = (Nat.add x1 y0)).
Definition term183 (x0 : nat) := (Peano.le x0 (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (Peano.le x1 x2).
Definition term269 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) -> (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (x1 = (NUMERAL 0)) -> (~ ((Nat.modulo x2 (NUMERAL (BIT1 0))) = (Nat.modulo x2 (NUMERAL 0)))) -> ((forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 (S y2)) = ((y1 = (S y2)) \/ (Peano.le y1 y2)))) -> False) x3.
Definition term445 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0).
Definition term423 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0).
Definition term224 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0).
Definition term202 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0).
Definition term178 := forall y0 : nat, ((fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0).
Definition term37 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.min x0 y0) = (@COND nat (Peano.le x0 y0) x0 y0)) x1.
Definition term358 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.pow x1 y0)) (Nat.pow x1 x2)) = (Nat.modulo x0 (Nat.pow x1 x2))) x3.
Definition term273 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 y0)) = (Nat.modulo x0 (Nat.pow x1 x2))) x3.
Definition term65 := @eq nat (NUMERAL 0).
Definition term258 (x0 : Prop) := ~ (~ x0).
Definition term582 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow y0 (Nat.add y1 y2)) = (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2))) x0.
Definition term576 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.modulo y0 (Nat.mul y1 y2)) y1) = (Nat.modulo y0 y1)) x0.
Definition term573 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (~ (Peano.le y1 y0)) -> (~ (exists y3 : nat, y1 = (Nat.add y0 y3))) -> (forall y3 : nat, forall y4 : nat, (Peano.le y3 y4) = (exists y5 : nat, y4 = (Nat.add y3 y5))) -> (forall y3 : nat, forall y4 : nat, (Peano.le y3 y4) \/ (Peano.le y4 y3)) -> False) x0.
Definition term285 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND Prop (y0 = (NUMERAL 0)) ((y1 = (NUMERAL 0)) -> y2 = (NUMERAL 0)) ((y0 = (NUMERAL (BIT1 0))) \/ (Peano.le y1 y2)))) x0.
Definition term266 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (y3 = (NUMERAL 0)) -> (~ (y2 = (NUMERAL 0))) -> (Peano.le y2 y1) -> (y1 = (NUMERAL 0)) -> (~ ((Nat.modulo y0 (NUMERAL (BIT1 0))) = (Nat.modulo y0 (NUMERAL 0)))) -> ((forall y4 : nat, (Peano.le y4 (NUMERAL 0)) = (y4 = (NUMERAL 0))) /\ (forall y4 : nat, forall y5 : nat, (Peano.le y4 (S y5)) = ((y4 = (S y5)) \/ (Peano.le y4 y5)))) -> False) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) x0.
Definition term22 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (Nat.modulo x1 x0) = x1.
Definition term544 (x0 : type1606) := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ ((fun y0 : type1606 => forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2)))) x0).
Definition term497 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1))) x2 (x1 x2).
Definition term339 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 x1).
Definition term515 (x0 : nat) (x1 : nat -> nat) := (fun y0 : nat => fun y1 : nat -> nat => forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2)))) x0 x1.
Definition term511 := forall y0 : nat, exists y1 : nat -> nat, (fun y2 : nat => fun y3 : nat -> nat => forall y4 : nat, (~ (Peano.le y2 y4)) \/ (y4 = (Nat.add y2 (y3 y4)))) y0 y1.
Definition term509 (x0 : type1586) := forall y0 : nat, exists y1 : nat -> nat, x0 y0 y1.
Definition term508 := forall y0 : nat, exists y1 : nat -> nat, forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2))).
Definition term486 (x0 : nat) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (Peano.le x0 y2)) \/ (y2 = (Nat.add x0 y3))) y0 y1.
Definition term484 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term481 (x0 : nat) := forall y0 : nat, exists y1 : nat, (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1)).
Definition term431 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0).
Definition term210 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0).
Definition term189 := fun y0 : nat => ((fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0).
Definition term75 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) x1.
Definition term186 (x0 : nat) := (fun y0 : nat => (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) x0.
Definition term471 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.add x1 y1)) y0.
Definition term163 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) \/ ((~ (x0 = (S x1))) /\ (~ (Peano.le x0 x1))).
Definition term477 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.le x1 x0)) \/ ((fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term480 (x0 : nat) := fun y0 : nat => exists y1 : nat, (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1)).
Definition term105 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) -> (Nat.modulo x1 (NUMERAL (BIT1 0))) = (Nat.modulo x1 (NUMERAL 0))) /\ ((~ (x0 = (NUMERAL 0))) -> (Nat.modulo x1 (NUMERAL 0)) = (Nat.modulo x1 (NUMERAL 0))).
Definition term280 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (exists y0 : nat, (Peano.lt (Nat.modulo x0 (Nat.pow x1 x2)) y0) /\ (Peano.le y0 (Nat.pow x1 (Nat.add x2 x3)))) -> Peano.lt (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 (Nat.add x2 x3)).
Definition term356 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term82 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term25 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) -> (Nat.modulo y1 y0) = y1.
Definition term14 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> (Nat.modulo x0 y0) = x0) x1.
Definition term417 (x0 : nat) (x1 : nat) := ((Peano.le x1 x0) \/ (~ (exists y0 : nat, x0 = (Nat.add x1 y0)))) /\ ((~ (Peano.le x1 x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term205 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term539 (x0 : type1606) := (fun y0 : type1606 => forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2)))) x0.
Definition term32 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (Peano.le x0 x1).
Definition term564 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq Prop ((x2 = (Nat.add x1 (x0 x1 x2))) \/ (~ (Peano.le x1 x2))).
Definition term155 (x0 : nat) := ((Peano.le x0 (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0)))) /\ ((~ (Peano.le x0 (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term91 (x0 : nat) (x1 : Prop) (x2 : nat) (x3 : nat) := (x1 -> (fun y0 : nat => (Nat.modulo x2 y0) = (Nat.modulo x2 (NUMERAL 0))) x0) /\ ((~ x1) -> (fun y0 : nat => (Nat.modulo x2 y0) = (Nat.modulo x2 (NUMERAL 0))) x3).
Definition term530 := fun y0 : type1606 => forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2))).
Definition term119 (x0 : nat) := (~ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (Nat.modulo x0 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False.
Definition term344 (x0 : nat) (x1 : nat) := False -> ((x0 = (NUMERAL 0)) -> (Nat.add x0 x1) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) -> (Nat.add (NUMERAL 0) x1) = (NUMERAL 0)).
Definition term534 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term167 (x0 : nat) (x1 : nat) := ((Peano.le x0 (S x1)) \/ ((~ (x0 = (S x1))) /\ (~ (Peano.le x0 x1)))) /\ ((~ (Peano.le x0 (S x1))) \/ ((x0 = (S x1)) \/ (Peano.le x0 x1))).
Definition term108 (x0 : Prop) := (~ x0) -> False.
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> (x1 = (NUMERAL 0)) -> (~ ((Nat.modulo x2 (NUMERAL (BIT1 0))) = (Nat.modulo x2 (NUMERAL 0)))) -> ~ ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term446 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0).
Definition term424 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0).
Definition term225 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0).
Definition term203 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0).
Definition term179 := (forall y0 : nat, (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0).
Definition term545 (x0 : type1606) := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (y1 = (Nat.add y0 (x0 y0 y1)))).
Definition term464 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term243 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term439 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0.
Definition term434 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0.
Definition term575 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (~ (Peano.le x0 x1)) -> (~ (exists y1 : nat, x0 = (Nat.add x1 y1))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) = (exists y3 : nat, y2 = (Nat.add y1 y3))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) -> False) x2.
Definition term109 (x0 : nat) := (~ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (Nat.modulo x0 (NUMERAL 0)))) -> False.
Definition term365 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term61 (x0 : nat) := (fun y0 : nat => (Nat.modulo (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term246 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 y0) x1.
Definition term43 (x0 : nat) := Nat.pow (NUMERAL 0) x0.
Definition term440 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0.
Definition term435 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0.
Definition term219 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0.
Definition term214 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0.
Definition term198 := forall y0 : nat, (fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0.
Definition term193 := forall y0 : nat, (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0.
Definition term250 (x0 : nat) := (~ (Peano.le x0 (NUMERAL 0))) -> Peano.le x0 (NUMERAL 0).
Definition term535 (x0 : Prop) (x1 : type961) := x0 /\ (exists y0 : type1606, x1 y0).
Definition term468 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term490 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1))) x1 x2.
Definition term312 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term98 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (Nat.modulo x1 (NUMERAL 0)) = (Nat.modulo x1 (NUMERAL 0)).
Definition term436 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1))).
Definition term553 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term255 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (~ (Peano.le x0 (NUMERAL 0)))).
Definition term29 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term256 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term319 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, ((x0 = (NUMERAL 0)) = y0) -> (y0 -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) = y1) -> ((~ y0) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = y2) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop y0 y1 y2)) x3.
Definition term176 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term360 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.modulo (Nat.modulo x0 (Nat.pow x2 (Nat.add x3 x1))) (Nat.pow x2 x3).
Definition term12 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.lt x0 y1) /\ (Peano.le y1 y0)) -> Peano.lt x0 y0.
Definition term548 := exists y0 : type1606, (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2)))).
Definition term416 (x0 : nat) (x1 : nat) := and ((Peano.le x1 x0) \/ (forall y0 : nat, ~ (x0 = (Nat.add x1 y0)))).
Definition term443 := fun y0 : nat => (forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term222 := fun y0 : nat => (forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ (forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term418 (x0 : nat) (x1 : nat) := ((Peano.le x1 x0) \/ (forall y0 : nat, ~ (x0 = (Nat.add x1 y0)))) /\ ((~ (Peano.le x1 x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term370 := ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term81 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term533 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term59 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term300 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term562 (x0 : type1606) (x1 : nat) (x2 : nat) := Nat.add x1 (x0 x1 x2).
Definition term181 := fun y0 : nat => (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)).
Definition term88 (x0 : nat -> Prop) (x1 : Prop) (x2 : nat) (x3 : nat) := x0 (@COND nat x1 x2 x3).
Definition term110 (x0 : nat) := ~ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (Nat.modulo x0 (NUMERAL 0))).
Definition term123 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term579 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.modulo x0 (Nat.mul x1 y0)) x1) = (Nat.modulo x0 x1).
Definition term68 (x0 : nat) := @COND nat (x0 = (NUMERAL 0)) (NUMERAL (BIT1 0)).
Definition term252 (x0 : Prop) := (~ x0) -> x0.
Definition term304 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term354 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => (Peano.lt (Nat.modulo x0 (Nat.pow x1 x2)) y0) /\ (Peano.le y0 (Nat.pow x1 (Nat.add x2 x3))).
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ~ ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False.
Definition term413 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (~ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term427 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) x1.
Definition term253 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (Peano.le x0 (NUMERAL 0))).
Definition term96 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term38 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x0 x1) x0 x1.
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.min x1 x2).
Definition term264 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term555 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x1 y0)) \/ (y0 = (Nat.add x1 (x0 x1 y0)))) x2.
Definition term474 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term473 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ (exists y0 : nat, (fun y1 : nat => x0 = (Nat.add x1 y1)) y0)).
Definition term282 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term160 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 (S x1))) \/ ((x0 = (S x1)) \/ (Peano.le x0 x1)).
Definition term551 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (x0 = (Nat.add x1 y0))) x2.
Definition term482 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term560 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term363 (x0 : nat) (x1 : nat) := (~ (exists y0 : nat, x0 = (Nat.add x1 y0))) -> False.
Definition term49 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 (@COND nat (x1 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term500 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 y2))) y0 (x1 y0).
Definition term94 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) -> (fun y0 : nat => (Nat.modulo x1 y0) = (Nat.modulo x1 (NUMERAL 0))) (NUMERAL (BIT1 0))) /\ ((~ (x0 = (NUMERAL 0))) -> (fun y0 : nat => (Nat.modulo x1 y0) = (Nat.modulo x1 (NUMERAL 0))) (NUMERAL 0)).
Definition term187 (x0 : nat) := (~ (Peano.le x0 (NUMERAL 0))) \/ (x0 = (NUMERAL 0)).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (((x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False.
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False.
Definition term455 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2)))).
Definition term454 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0)).
Definition term433 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) /\ ((~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1)))).
Definition term432 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0)).
Definition term234 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ (forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term233 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0)).
Definition term212 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) /\ ((~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0)))).
Definition term211 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0)).
Definition term191 := @eq Prop (forall y0 : nat, ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))).
Definition term190 := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0)).
Definition term512 := exists y0 : type1606, forall y1 : nat, (fun y2 : nat => fun y3 : nat -> nat => forall y4 : nat, (~ (Peano.le y2 y4)) \/ (y4 = (Nat.add y2 (y3 y4)))) y1 (y0 y1).
Definition term510 (x0 : type1586) := exists y0 : type1606, forall y1 : nat, x0 y1 (y0 y1).
Definition term506 (x0 : nat) := exists y0 : nat -> nat, forall y1 : nat, (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 (y0 y1))).
Definition term487 (x0 : nat) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (Peano.le x0 y2)) \/ (y2 = (Nat.add x0 y3))) y1 (y0 y1).
Definition term485 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term517 (x0 : nat) := fun y0 : nat -> nat => (fun y1 : nat => fun y2 : nat -> nat => forall y3 : nat, (~ (Peano.le y1 y3)) \/ (y3 = (Nat.add y1 (y2 y3)))) x0 y0.
Definition term488 (x0 : nat) := fun y0 : nat => fun y1 : nat => (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1)).
Definition term475 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ ((fun y0 : nat => x0 = (Nat.add x1 y0)) x2).
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term373 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term120 (x0 : nat) := (~ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (Nat.modulo x0 (NUMERAL 0)))) -> ~ ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term245 (x0 : nat) := fun y0 : nat => Peano.le x0 y0.
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.modulo (Nat.modulo x0 (Nat.pow x2 x1)) (Nat.pow x2 x3)).
Definition term66 (x0 : nat) := @COND nat (x0 = (NUMERAL 0)).
Definition term501 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 (x1 y0))).
Definition term584 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1))) x1.
Definition term578 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.modulo x0 (Nat.mul y0 y1)) y0) = (Nat.modulo x0 y0)) x1.
Definition term574 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ (Peano.le y0 x0)) -> (~ (exists y2 : nat, y0 = (Nat.add x0 y2))) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) = (exists y4 : nat, y3 = (Nat.add y2 y4))) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) \/ (Peano.le y3 y2)) -> False) x1.
Definition term554 (x0 : type1606) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (y1 = (Nat.add y0 (x0 y0 y1)))) x1.
Definition term287 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND Prop (x0 = (NUMERAL 0)) ((y0 = (NUMERAL 0)) -> y1 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le y0 y1)))) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1) x1.
Definition term345 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (False -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) = ((x1 = (NUMERAL 0)) -> (Nat.add (NUMERAL 0) x2) = (NUMERAL 0))) -> ((~ False) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = x3) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop False ((x1 = (NUMERAL 0)) -> (Nat.add (NUMERAL 0) x2) = (NUMERAL 0)) x3).
Definition term559 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> Peano.le x0 x1.
Definition term404 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 = (Nat.add x1 y0)) x2.
Definition term62 (x0 : nat) := Nat.modulo (NUMERAL 0) x0.
Definition term375 (x0 : nat) (x1 : nat) := imp (~ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.modulo (Nat.modulo x0 (Nat.pow x2 x1)) (Nat.pow x2 x3).
Definition term164 (x0 : nat) (x1 : nat) := and ((Peano.le x0 (S x1)) \/ (~ ((x0 = (S x1)) \/ (Peano.le x0 x1)))).
Definition term536 (x0 : Prop) (x1 : type961) := exists y0 : type1606, x0 /\ (x1 y0).
Definition term147 (x0 : nat) := fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term45 := Nat.pow (NUMERAL 0).
Definition term41 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term532 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (exists y0 : type1606, forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2)))).
Definition term397 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term441 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term516 (x0 : nat) (x1 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat, (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 (y0 y1)))) x1.
Definition term33 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x0 x1)).
Definition term396 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term499 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (x2 = (Nat.add x0 (x1 x2))).
Definition term89 (x0 : nat) (x1 : Prop) (x2 : nat -> Prop) (x3 : nat) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term340 (x0 : nat) := @eq nat (Nat.add (NUMERAL 0) x0).
Definition term283 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term527 (x0 : type1606) := forall y0 : nat, (fun y1 : nat => fun y2 : nat -> nat => forall y3 : nat, (~ (Peano.le y1 y3)) \/ (y3 = (Nat.add y1 (y2 y3)))) y0 (x0 y0).
Definition term100 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term184 (x0 : nat) := and ((fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) x0).
Definition term327 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term188 (x0 : nat) := ((fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) x0) /\ ((fun y0 : nat => (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) x0).
Definition term201 := and ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))).
Definition term279 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 x2).
Definition term71 := Nat.modulo (NUMERAL 0).
Definition term492 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 y2))) x1 y0.
Definition term524 (x0 : type1606) (x1 : nat) := forall y0 : nat, (~ (Peano.le x1 y0)) \/ (y0 = (Nat.add x1 (x0 x1 y0))).
Definition term503 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 (x1 y0))).
Definition term103 (x0 : nat) (x1 : nat) := and ((x0 = (NUMERAL 0)) -> (fun y0 : nat => (Nat.modulo x1 y0) = (Nat.modulo x1 (NUMERAL 0))) (NUMERAL (BIT1 0))).
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) -> (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (x1 = (NUMERAL 0)) -> (~ ((Nat.modulo x2 (NUMERAL (BIT1 0))) = (Nat.modulo x2 (NUMERAL 0)))) -> ~ ((forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 (S y2)) = ((y1 = (S y2)) \/ (Peano.le y1 y2)))).
Definition term129 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) -> (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (x1 = (NUMERAL 0)) -> (~ ((Nat.modulo x2 (NUMERAL (BIT1 0))) = (Nat.modulo x2 (NUMERAL 0)))) -> ((forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 (S y2)) = ((y1 = (S y2)) \/ (Peano.le y1 y2)))) -> False.
Definition term34 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term192 := fun y0 : nat => (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0.
Definition term412 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term347 (x0 : nat) := or (x0 = (NUMERAL (BIT1 0))).
Definition term581 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.modulo x0 (Nat.mul x2 x1)) x2.
Definition term63 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL (BIT1 0))) = (NUMERAL 0)) x0.
Definition term295 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))).
Definition term104 (x0 : nat) (x1 : nat) := and ((x0 = (NUMERAL 0)) -> (Nat.modulo x1 (NUMERAL (BIT1 0))) = (Nat.modulo x1 (NUMERAL 0))).
Definition term369 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (((x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False) -> ((x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False) -> (x0 = (NUMERAL 0)) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (x2 = (NUMERAL 0)) -> (~ ((Nat.modulo x3 (NUMERAL (BIT1 0))) = (Nat.modulo x3 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0) x2.
Definition term491 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x1 x0)) \/ (x0 = (Nat.add x1 y0))) x2.
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo x0 (Nat.pow x1 x2).
Definition term263 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> x0 = (NUMERAL 0).
Definition term593 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.modulo (Nat.modulo x0 (Nat.pow x2 (Nat.add x3 x1))) (Nat.pow x2 x3)).
Definition term529 := fun y0 : type1606 => forall y1 : nat, (fun y2 : nat => fun y3 : nat -> nat => forall y4 : nat, (~ (Peano.le y2 y4)) \/ (y4 = (Nat.add y2 (y3 y4)))) y1 (y0 y1).
Definition term505 (x0 : nat) := fun y0 : nat -> nat => forall y1 : nat, (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 (y0 y1))).
Definition term504 (x0 : nat) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (Peano.le x0 y2)) \/ (y2 = (Nat.add x0 y3))) y1 (y0 y1).
Definition term541 := exists y0 : type1606, (fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0.
Definition term383 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (~ (Peano.le x0 x1)) -> (~ (exists y1 : nat, x0 = (Nat.add x1 y1))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) = (exists y3 : nat, y2 = (Nat.add y1 y3))) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)).
Definition term382 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (~ (Peano.le x0 x1)) -> (~ (exists y1 : nat, x0 = (Nat.add x1 y1))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) = (exists y3 : nat, y2 = (Nat.add y1 y3))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) -> False.
Definition term385 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (~ (Peano.le x0 x1)) -> (~ (exists y1 : nat, x0 = (Nat.add x1 y1))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) = (exists y3 : nat, y2 = (Nat.add y1 y3))) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)).
Definition term384 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (~ (Peano.le x0 x1)) -> (~ (exists y1 : nat, x0 = (Nat.add x1 y1))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) = (exists y3 : nat, y2 = (Nat.add y1 y3))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) -> False.
Definition term521 := @eq Prop (forall y0 : nat, exists y1 : nat -> nat, forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2)))).
Definition term520 := @eq Prop (forall y0 : nat, exists y1 : nat -> nat, (fun y2 : nat => fun y3 : nat -> nat => forall y4 : nat, (~ (Peano.le y2 y4)) \/ (y4 = (Nat.add y2 (y3 y4)))) y0 y1).
Definition term496 (x0 : nat) := @eq Prop (forall y0 : nat, exists y1 : nat, (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1))).
Definition term495 (x0 : nat) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (Peano.le x0 y2)) \/ (y2 = (Nat.add x0 y3))) y0 y1).
Definition term368 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> ((~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term11 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.lt x0 y0) /\ (Peano.le y0 x1)) -> Peano.lt x0 x1.
Definition term95 (x0 : nat) := (fun y0 : nat => (Nat.modulo x0 y0) = (Nat.modulo x0 (NUMERAL 0))) (NUMERAL 0).
Definition term438 (x0 : nat) := and (forall y0 : nat, (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))).
Definition term217 (x0 : nat) := and (forall y0 : nat, (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))).
Definition term196 := and (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term172 := and (forall y0 : nat, ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))).
Definition term154 := and (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))).
Definition term419 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) /\ ((~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))).
Definition term310 (x0 : nat) (x1 : nat) (x2 : nat) := @COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))).
Definition term362 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Nat.modulo (Nat.modulo x1 (Nat.pow x2 x0)) (Nat.pow x2 x3)) = (Nat.modulo x1 (Nat.pow x2 x3))).
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Nat.modulo (Nat.modulo x1 (Nat.pow x2 x3)) (Nat.pow x2 x0)) = (Nat.modulo x1 (Nat.pow x2 x3))).
Definition term572 (x0 : type1606) (x1 : nat) (x2 : nat) := (x2 = (Nat.add x1 (x0 x1 x2))) -> False.
Definition term31 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term338 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term206 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) x1.
Definition term76 := @COND nat True (NUMERAL 0).
Definition term466 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term540 := fun y0 : type1606 => (fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0.
Definition term165 (x0 : nat) (x1 : nat) := and ((Peano.le x0 (S x1)) \/ ((~ (x0 = (S x1))) /\ (~ (Peano.le x0 x1)))).
Definition term592 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.modulo (Nat.modulo x0 (Nat.mul (Nat.pow x2 x3) (Nat.pow x2 x1))) (Nat.pow x2 x3).
Definition term588 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.modulo x0 (Nat.pow x1 (Nat.add x2 x3)).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.modulo x0 (Nat.pow x1 (Nat.min x2 x3)).
Definition term218 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 (S y1))) \/ ((x0 = (S y1)) \/ (Peano.le x0 y1))) y0.
Definition term213 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0.
Definition term197 := fun y0 : nat => (fun y1 : nat => (~ (Peano.le y1 (NUMERAL 0))) \/ (y1 = (NUMERAL 0))) y0.
Definition term87 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> (Peano.le x0 x1) = False.
Definition term359 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.pow x1 y0)) (Nat.pow x1 x2)) = (Nat.modulo x0 (Nat.pow x1 x2))) (Nat.add x2 x3).
Definition term274 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 y0)) = (Nat.modulo x0 (Nat.pow x1 x2))) (Nat.add x2 x3).
Definition term598 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.modulo y0 (Nat.pow y1 y2)) (Nat.pow y1 y3)) = (Nat.modulo y0 (Nat.pow y1 (Nat.min y2 y3))).
Definition term597 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.modulo x0 (Nat.pow y0 y1)) (Nat.pow y0 y2)) = (Nat.modulo x0 (Nat.pow y0 (Nat.min y1 y2))).
Definition term596 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.modulo x0 (Nat.pow x1 y0)) (Nat.pow x1 y1)) = (Nat.modulo x0 (Nat.pow x1 (Nat.min y0 y1))).
Definition term583 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)).
Definition term577 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.modulo x0 (Nat.mul y0 y1)) y0) = (Nat.modulo x0 y0).
Definition term528 (x0 : type1606) := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (y1 = (Nat.add y0 (x0 y0 y1))).
Definition term463 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2)).
Definition term458 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2))).
Definition term422 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ ((~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term400 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2)).
Definition term393 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (~ (Peano.le y1 y0)) -> (~ (exists y3 : nat, y1 = (Nat.add y0 y3))) -> (forall y3 : nat, forall y4 : nat, (Peano.le y3 y4) = (exists y5 : nat, y4 = (Nat.add y3 y5))) -> ~ (forall y3 : nat, forall y4 : nat, (Peano.le y3 y4) \/ (Peano.le y4 y3)).
Definition term392 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (~ (Peano.le y1 y0)) -> (~ (exists y3 : nat, y1 = (Nat.add y0 y3))) -> (forall y3 : nat, forall y4 : nat, (Peano.le y3 y4) = (exists y5 : nat, y4 = (Nat.add y3 y5))) -> (forall y3 : nat, forall y4 : nat, (Peano.le y3 y4) \/ (Peano.le y4 y3)) -> False.
Definition term389 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ (Peano.le y0 x0)) -> (~ (exists y2 : nat, y0 = (Nat.add x0 y2))) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) = (exists y4 : nat, y3 = (Nat.add y2 y4))) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) \/ (Peano.le y3 y2)).
Definition term388 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ (Peano.le y0 x0)) -> (~ (exists y2 : nat, y0 = (Nat.add x0 y2))) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) = (exists y4 : nat, y3 = (Nat.add y2 y4))) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) \/ (Peano.le y3 y2)) -> False.
Definition term371 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term286 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND Prop (x0 = (NUMERAL 0)) ((y0 = (NUMERAL 0)) -> y1 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le y0 y1))).
Definition term242 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term237 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1))).
Definition term171 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ ((~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term150 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term144 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (y3 = (NUMERAL 0)) -> (~ (y2 = (NUMERAL 0))) -> (Peano.le y2 y1) -> (y1 = (NUMERAL 0)) -> (~ ((Nat.modulo y0 (NUMERAL (BIT1 0))) = (Nat.modulo y0 (NUMERAL 0)))) -> ~ ((forall y4 : nat, (Peano.le y4 (NUMERAL 0)) = (y4 = (NUMERAL 0))) /\ (forall y4 : nat, forall y5 : nat, (Peano.le y4 (S y5)) = ((y4 = (S y5)) \/ (Peano.le y4 y5)))).
Definition term143 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (y3 = (NUMERAL 0)) -> (~ (y2 = (NUMERAL 0))) -> (Peano.le y2 y1) -> (y1 = (NUMERAL 0)) -> (~ ((Nat.modulo y0 (NUMERAL (BIT1 0))) = (Nat.modulo y0 (NUMERAL 0)))) -> ((forall y4 : nat, (Peano.le y4 (NUMERAL 0)) = (y4 = (NUMERAL 0))) /\ (forall y4 : nat, forall y5 : nat, (Peano.le y4 (S y5)) = ((y4 = (S y5)) \/ (Peano.le y4 y5)))) -> False.
Definition term140 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (y2 = (NUMERAL 0)) -> (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (y0 = (NUMERAL 0)) -> (~ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (Nat.modulo x0 (NUMERAL 0)))) -> ~ ((forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (Peano.le y3 (S y4)) = ((y3 = (S y4)) \/ (Peano.le y3 y4)))).
Definition term139 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (y2 = (NUMERAL 0)) -> (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (y0 = (NUMERAL 0)) -> (~ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (Nat.modulo x0 (NUMERAL 0)))) -> ((forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (Peano.le y3 (S y4)) = ((y3 = (S y4)) \/ (Peano.le y3 y4)))) -> False.
Definition term136 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) -> (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (x0 = (NUMERAL 0)) -> (~ ((Nat.modulo x1 (NUMERAL (BIT1 0))) = (Nat.modulo x1 (NUMERAL 0)))) -> ~ ((forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.le y2 (S y3)) = ((y2 = (S y3)) \/ (Peano.le y2 y3)))).
Definition term135 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) -> (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (x0 = (NUMERAL 0)) -> (~ ((Nat.modulo x1 (NUMERAL (BIT1 0))) = (Nat.modulo x1 (NUMERAL 0)))) -> ((forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.le y2 (S y3)) = ((y2 = (S y3)) \/ (Peano.le y2 y3)))) -> False.
Definition term24 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) -> (Nat.modulo y1 y0) = y1.
Definition term17 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0.
Definition term13 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1.
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1.
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term465 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term343 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (Nat.add (NUMERAL 0) x1) = (NUMERAL 0).
Definition term317 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (Nat.add x0 x1) = (NUMERAL 0).
Definition term97 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (fun y0 : nat => (Nat.modulo x1 y0) = (Nat.modulo x1 (NUMERAL 0))) (NUMERAL 0).
Definition term294 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term405 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => x0 = (Nat.add x1 y0)) x2).
Definition term452 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))) x0).
Definition term231 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0).
Definition term40 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term367 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term44 (x0 : nat) := @COND nat (x0 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term401 (x0 : nat -> Prop) := ~ (ex x0).
Definition term268 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) -> (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (x0 = (NUMERAL 0)) -> (~ ((Nat.modulo x1 (NUMERAL (BIT1 0))) = (Nat.modulo x1 (NUMERAL 0)))) -> ((forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.le y2 (S y3)) = ((y2 = (S y3)) \/ (Peano.le y2 y3)))) -> False) x2.
Definition term426 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term275 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.modulo (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 (Nat.add x2 x3)).
Definition term267 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (y2 = (NUMERAL 0)) -> (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (y0 = (NUMERAL 0)) -> (~ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (Nat.modulo x0 (NUMERAL 0)))) -> ((forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (Peano.le y3 (S y4)) = ((y3 = (S y4)) \/ (Peano.le y3 y4)))) -> False) x1.
Definition term377 (x0 : nat) (x1 : nat) := (~ (exists y0 : nat, x0 = (Nat.add x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term470 (x0 : nat) (x1 : nat) := exists y0 : nat, (~ (Peano.le x1 x0)) \/ ((fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term333 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((x0 = (NUMERAL 0)) = x2) -> (x2 -> ((Nat.add x0 x1) = (NUMERAL 0)) = y0) -> ((x0 = (NUMERAL 0)) -> (Nat.add x0 x1) = (NUMERAL 0)) = (x2 -> y0)) x3.
Definition term262 (x0 : nat) := (Peano.le x0 (NUMERAL 0)) -> x0 = (NUMERAL 0).
Definition term569 (x0 : type1606) (x1 : nat) (x2 : nat) := (~ (x2 = (Nat.add x1 (x0 x1 x2)))) -> x2 = (Nat.add x1 (x0 x1 x2)).
Definition term448 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2)).
Definition term447 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2))).
Definition term399 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2)).
Definition term182 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) x0.
Definition term324 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) (x5 : Prop) := ((x0 = (NUMERAL 0)) = x3) -> (x3 -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) = x4) -> ((~ x3) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = x5) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop x3 x4 x5).
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) -> (Nat.modulo y0 x0) = y0) x1.
Definition term518 (x0 : nat) := exists y0 : nat -> nat, (fun y1 : nat => fun y2 : nat -> nat => forall y3 : nat, (~ (Peano.le y1 y3)) \/ (y3 = (Nat.add y1 (y2 y3)))) x0 y0.
Definition term248 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.le x0 y0) x1).
Definition term547 := fun y0 : type1606 => (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2)))).
Definition term299 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term291 (x0 : nat) (x1 : nat) (x2 : nat) := @COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2)).
Definition term355 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.lt (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 (Nat.add x2 x3)).
Definition term86 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo x0 (@COND nat (x1 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term519 := fun y0 : nat => exists y1 : nat -> nat, (fun y2 : nat => fun y3 : nat -> nat => forall y4 : nat, (~ (Peano.le y2 y4)) \/ (y4 = (Nat.add y2 (y3 y4)))) y0 y1.
Definition term64 (x0 : nat) := Nat.modulo x0 (NUMERAL (BIT1 0)).
Definition term402 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term568 (x0 : type1606) (x1 : nat) (x2 : nat) := (Peano.le x1 x2) -> x2 = (Nat.add x1 (x0 x1 x2)).
Definition term590 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.modulo (Nat.modulo x0 (Nat.pow x1 (Nat.add x2 x3))).
Definition term36 (x0 : nat) := forall y0 : nat, (Nat.min x0 y0) = (@COND nat (Peano.le x0 y0) x0 y0).
Definition term507 := fun y0 : nat => exists y1 : nat -> nat, forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2))).
Definition term469 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (exists y0 : nat, (fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term60 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term585 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0)).
Definition term148 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term152 := fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term425 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1))).
Definition term381 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term85 := @COND nat False (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term350 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ False) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = True) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop False ((x1 = (NUMERAL 0)) -> (Nat.add (NUMERAL 0) x2) = (NUMERAL 0)) True).
Definition term394 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.le x0 x1).
Definition term335 (x0 : nat) (x1 : nat) (x2 : Prop) := ((x1 = (NUMERAL 0)) = (x1 = (NUMERAL 0))) -> ((x1 = (NUMERAL 0)) -> ((Nat.add x1 x0) = (NUMERAL 0)) = x2) -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x0) = (NUMERAL 0)) = ((x1 = (NUMERAL 0)) -> x2).
Definition term357 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.pow x1 y0)) (Nat.pow x1 x2)) = (Nat.modulo x0 (Nat.pow x1 x2)).
Definition term332 (x0 : nat) (x1 : nat) (x2 : Prop) := forall y0 : Prop, ((x0 = (NUMERAL 0)) = x2) -> (x2 -> ((Nat.add x0 x1) = (NUMERAL 0)) = y0) -> ((x0 = (NUMERAL 0)) -> (Nat.add x0 x1) = (NUMERAL 0)) = (x2 -> y0).
Definition term328 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term322 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := forall y0 : Prop, ((x0 = (NUMERAL 0)) = x3) -> (x3 -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) = x4) -> ((~ x3) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = y0) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop x3 x4 y0).
Definition term493 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 y2))) x1 y0.
Definition term247 (x0 : nat) := (fun y0 : nat => Peano.le x0 y0) (NUMERAL 0).
Definition term185 (x0 : nat) := and ((Peano.le x0 (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0)))).
Definition term352 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 x2)) /\ (Peano.le (Nat.pow x1 x2) (Nat.pow x1 (Nat.add x2 x3))).
Definition term430 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) x1) /\ ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))) x1).
Definition term209 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) x1) /\ ((fun y0 : nat => (~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1).
Definition term177 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo x0 (@COND nat ((@COND nat (Peano.le x1 x2) x1 x2) = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term47 (x0 : nat) (x1 : nat) := Nat.modulo x0 (@COND nat (x1 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term77 (x0 : nat) := @COND nat True (NUMERAL 0) x0.
Definition term580 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.mul x1 y0)) x1) = (Nat.modulo x0 x1)) x2.
Definition term249 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term472 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.add x1 y1)) y0.
Definition term549 (x0 : type1606) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x2)) \/ (x2 = (Nat.add x1 (x0 x1 x2))).
Definition term272 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 y0)) = (Nat.modulo x0 (Nat.pow x1 x2)).
Definition term591 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.modulo (Nat.modulo x0 (Nat.mul (Nat.pow x2 x1) (Nat.pow x2 x3))).
Definition term118 (x0 : nat) := imp (~ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (Nat.modulo x0 (NUMERAL 0)))).
Definition term513 := fun y0 : nat => fun y1 : nat -> nat => forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2))).
Definition term330 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((x0 = (NUMERAL 0)) = y0) -> (y0 -> ((Nat.add x0 x1) = (NUMERAL 0)) = y1) -> ((x0 = (NUMERAL 0)) -> (Nat.add x0 x1) = (NUMERAL 0)) = (y0 -> y1).
Definition term329 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term320 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, forall y1 : Prop, ((x0 = (NUMERAL 0)) = x3) -> (x3 -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) = y0) -> ((~ x3) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = y1) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop x3 y0 y1).
Definition term316 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, ((x0 = (NUMERAL 0)) = y0) -> (y0 -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) = y1) -> ((~ y0) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = y2) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop y0 y1 y2).
Definition term315 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND Prop x0 x1 x2) = (@COND Prop y0 y1 y2).
Definition term314 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term116 := ~ ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term56 (x0 : nat) (x1 : nat) := @COND nat ((@COND nat (Peano.le x0 x1) x0 x1) = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term194 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term21 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) -> (Nat.modulo x1 x0) = x1.
Definition term173 := (forall y0 : nat, ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, forall y1 : nat, ((Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ ((~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term117 := (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term161 (x0 : nat) (x1 : nat) := or (Peano.le x0 (S x1)).
Definition term353 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, (Peano.lt (Nat.modulo x0 (Nat.pow x1 x2)) y0) /\ (Peano.le y0 (Nat.pow x1 (Nat.add x2 x3))).
Definition term538 := exists y0 : type1606, (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) /\ ((fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0).
Definition term349 (x0 : nat) (x1 : nat) (x2 : nat) := (~ False) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = True.
Definition term409 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ (x0 = (Nat.add x1 y0)).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0.
Definition term410 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term366 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ (Peano.le x1 x2)) -> (~ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term180 := fun y0 : nat => (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term70 := @COND nat True (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term199 := forall y0 : nat, (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)).
Definition term556 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> ~ (Peano.le x0 x1).
Definition term318 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)).
Definition term336 (x0 : nat) (x1 : nat) (x2 : Prop) := ((x1 = (NUMERAL 0)) -> ((Nat.add x1 x0) = (NUMERAL 0)) = x2) -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x0) = (NUMERAL 0)) = ((x1 = (NUMERAL 0)) -> x2).
Definition term270 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (@COND nat (Peano.le x1 x2) x1 x2).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.modulo x0 (Nat.pow x1 x2)).
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (x1 = (NUMERAL 0)) -> (~ ((Nat.modulo x2 (NUMERAL (BIT1 0))) = (Nat.modulo x2 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False.
Definition term442 (x0 : nat) := (forall y0 : nat, (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) /\ (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))).
Definition term221 (x0 : nat) := (forall y0 : nat, (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) /\ (forall y0 : nat, (~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0))).
Definition term200 := (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term489 (x0 : nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1))) x1.
Definition term8 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> Peano.lt x0 x1.
Definition term121 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (~ ((Nat.modulo x1 (NUMERAL (BIT1 0))) = (Nat.modulo x1 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False.
Definition term289 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> y0 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 y0)))) x2.
Definition term337 := Nat.add (NUMERAL 0).
Definition term460 := and (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))).
Definition term239 := and (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))).
Definition term498 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x0 x2)) \/ (x2 = (Nat.add x0 y0))) (x1 x2).
Definition term309 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 x1) (Nat.pow x0 (Nat.add x1 x2)).
Definition term78 (x0 : nat) (x1 : nat) := @eq nat (@COND nat (Peano.le x0 x1) x0 x1).
Definition term215 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0))).
Definition term146 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term303 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.pow x1 x2) = (NUMERAL 0))) -> (Peano.lt (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 x2)) = True.
Definition term220 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term403 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term461 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0.
Definition term456 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0.
Definition term240 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0.
Definition term235 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0.
Definition term284 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term323 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((x0 = (NUMERAL 0)) = x3) -> (x3 -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) = x4) -> ((~ x3) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = y0) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop x3 x4 y0)) x5.
Definition term552 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term451 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term449 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) x0.
Definition term296 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term292 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term281 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term230 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term228 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) x0.
Definition term35 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.min y0 y1) = (@COND nat (Peano.le y0 y1) y0 y1)) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (Nat.modulo y1 y0) = y1) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1) x0.
Definition term502 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 y2))) y0 (x1 y0).
Definition term537 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (exists y0 : type1606, (fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0).
Definition term566 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term514 (x0 : nat) := (fun y0 : nat => fun y1 : nat -> nat => forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2)))) x0.
Definition term159 (x0 : nat) (x1 : nat) := (~ (x0 = (S x1))) /\ (~ (Peano.le x0 x1)).
Definition term23 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) -> (Nat.modulo y0 x0) = y0.
Definition term531 := exists y0 : type1606, forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2))).
Definition term351 (x0 : nat) (x1 : nat) := @COND Prop False ((x0 = (NUMERAL 0)) -> (Nat.add (NUMERAL 0) x1) = (NUMERAL 0)) True.
Definition term101 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (fun y0 : nat => (Nat.modulo x1 y0) = (Nat.modulo x1 (NUMERAL 0))) (NUMERAL (BIT1 0)).
Definition term348 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ True.
Definition term346 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := ((~ False) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = x3) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop False ((x1 = (NUMERAL 0)) -> (Nat.add (NUMERAL 0) x2) = (NUMERAL 0)) x3).
Definition term313 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term595 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Nat.modulo (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 y0)) = (Nat.modulo x0 (Nat.pow x1 (Nat.min x2 y0))).
Definition term411 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term334 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := ((x0 = (NUMERAL 0)) = x2) -> (x2 -> ((Nat.add x0 x1) = (NUMERAL 0)) = x3) -> ((x0 = (NUMERAL 0)) -> (Nat.add x0 x1) = (NUMERAL 0)) = (x2 -> x3).
Definition term586 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) x2.
Definition term414 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (forall y0 : nat, ~ (x0 = (Nat.add x1 y0))).
Definition term594 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo x0 (Nat.pow x1 x2)).
Definition term204 (x0 : nat) := fun y0 : nat => (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0))).
Definition term522 (x0 : type1606) (x1 : nat) := (fun y0 : nat => fun y1 : nat -> nat => forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2)))) x1 (x0 x1).
Definition term341 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> ((Nat.add x0 x1) = (NUMERAL 0)) = ((Nat.add (NUMERAL 0) x1) = (NUMERAL 0)).
Definition term302 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.modulo x0 x1) x1) = True.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x1 x0) /\ (Peano.le x0 x2)) -> Peano.lt x1 x2.
Definition term378 (x0 : nat) (x1 : nat) := imp (~ (Peano.le x0 x1)).
Definition term208 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term589 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.modulo x0 (Nat.mul (Nat.pow x2 x1) (Nat.pow x2 x3)).
Definition term153 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term558 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) \/ (Peano.le x0 x1)).
Definition term494 (x0 : nat) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (Peano.le x0 y2)) \/ (y2 = (Nat.add x0 y3))) y0 y1.
Definition term374 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term459 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0).
Definition term437 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0).
Definition term238 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0).
Definition term216 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.le x0 (S y1)) \/ ((~ (x0 = (S y1))) /\ (~ (Peano.le x0 y1)))) y0).
Definition term195 := and (forall y0 : nat, (fun y1 : nat => (Peano.le y1 (NUMERAL 0)) \/ (~ (y1 = (NUMERAL 0)))) y0).
Definition term523 (x0 : type1606) (x1 : nat) := (fun y0 : nat -> nat => forall y1 : nat, (~ (Peano.le x1 y1)) \/ (y1 = (Nat.add x1 (y0 y1)))) (x0 x1).
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (x1 = (NUMERAL 0)) -> (~ ((Nat.modulo x2 (NUMERAL (BIT1 0))) = (Nat.modulo x2 (NUMERAL 0)))) -> ~ ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term80 (x0 : nat) (x1 : nat) := @COND nat ((@COND nat (Peano.le x0 x1) x0 x1) = (NUMERAL 0)) (NUMERAL (BIT1 0)).
Definition term450 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) x0).
Definition term229 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) x0).
Definition term83 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term301 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term298 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term168 (x0 : nat) := fun y0 : nat => ((Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) /\ ((~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0))).
Definition term325 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((x0 = (NUMERAL 0)) = False) -> (False -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) = x3) -> ((~ False) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = x4) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop False x3 x4).
Definition term587 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term307 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 x2).
Definition term476 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ (x0 = (Nat.add x1 x2)).
Definition term74 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x0 x1).
Definition term99 (x0 : nat) := (fun y0 : nat => (Nat.modulo x0 y0) = (Nat.modulo x0 (NUMERAL 0))) (NUMERAL (BIT1 0)).
Definition term429 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term260 (x0 : nat) := imp (~ (~ (Peano.le x0 (NUMERAL 0)))).
Definition term342 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) -> ((Nat.add x0 x1) = (NUMERAL 0)) = ((Nat.add (NUMERAL 0) x1) = (NUMERAL 0))) -> ((x0 = (NUMERAL 0)) -> (Nat.add x0 x1) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) -> (Nat.add (NUMERAL 0) x1) = (NUMERAL 0)).
Definition term122 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (~ ((Nat.modulo x1 (NUMERAL (BIT1 0))) = (Nat.modulo x1 (NUMERAL 0)))) -> ~ ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term115 := ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False.
Definition term69 := @COND nat True (NUMERAL (BIT1 0)).
Definition term10 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt x0 y0) /\ (Peano.le y0 x1).
Definition term543 := @eq Prop ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (exists y0 : type1606, forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2))))).
Definition term542 := @eq Prop ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (exists y0 : type1606, (fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0)).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term306 (x0 : nat) (x1 : nat) := ~ ((Nat.pow x0 x1) = (NUMERAL 0)).
Definition term444 := forall y0 : nat, (forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term223 := forall y0 : nat, (forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ (forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term380 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> (~ (exists y0 : nat, x0 = (Nat.add x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term73 := Peano.le (NUMERAL 0).
Definition term563 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x2)) \/ (x2 = (Nat.add x1 (x0 x1 x2)))).
Definition term290 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term271 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.modulo x0 (Nat.pow x1 (@COND nat (Peano.le x2 x3) x2 x3)).
Definition term132 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) -> (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (x1 = (NUMERAL 0)) -> (~ ((Nat.modulo x2 (NUMERAL (BIT1 0))) = (Nat.modulo x2 (NUMERAL 0)))) -> ~ ((forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 (S y2)) = ((y1 = (S y2)) \/ (Peano.le y1 y2)))).
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) -> (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (x1 = (NUMERAL 0)) -> (~ ((Nat.modulo x2 (NUMERAL (BIT1 0))) = (Nat.modulo x2 (NUMERAL 0)))) -> ((forall y1 : nat, (Peano.le y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 (S y2)) = ((y1 = (S y2)) \/ (Peano.le y1 y2)))) -> False.
Definition term408 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (x0 = (Nat.add x1 y0)).
Definition term428 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) x1).
Definition term207 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) x1).
Definition term407 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term308 (x0 : nat) (x1 : nat) (x2 : nat) := and (Peano.lt (Nat.modulo x0 (Nat.pow x1 x2)) (Nat.pow x1 x2)).
Definition term415 (x0 : nat) (x1 : nat) := and ((Peano.le x1 x0) \/ (~ (exists y0 : nat, x0 = (Nat.add x1 y0)))).
Definition term42 (x0 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL 0) y0) = (@COND nat (y0 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0))) x0.
Definition term479 (x0 : nat) (x1 : nat) := exists y0 : nat, (~ (Peano.le x1 x0)) \/ (x0 = (Nat.add x1 y0)).
Definition term55 (x0 : nat) (x1 : nat) := Nat.pow (NUMERAL 0) (@COND nat (Peano.le x0 x1) x0 x1).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.modulo x0 (@COND nat (x1 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0))) (@COND nat (x2 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term254 (x0 : nat) := @eq Prop ((~ (Peano.le x0 (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term102 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (Nat.modulo x1 (NUMERAL (BIT1 0))) = (Nat.modulo x1 (NUMERAL 0)).
Definition term406 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (x0 = (Nat.add x1 x2)).
Definition term158 (x0 : nat) (x1 : nat) := ~ ((x0 = (S x1)) \/ (Peano.le x0 x1)).
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term90 (x0 : nat) (x1 : Prop) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Nat.modulo x0 y0) = (Nat.modulo x0 (NUMERAL 0))) (@COND nat x1 x2 x3).
Definition term297 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term321 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 = (NUMERAL 0)) = x3) -> (x3 -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) = y0) -> ((~ x3) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = y1) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop x3 y0 y1)) x4.
Definition term107 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.modulo x1 (@COND nat (x0 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0))) = (Nat.modulo x1 (NUMERAL 0))).
Definition term565 (x0 : type1606) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x2))) -> x2 = (Nat.add x1 (x0 x1 x2)).
Definition term462 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0.
Definition term457 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0.
Definition term241 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 (S y2))) \/ ((y1 = (S y2)) \/ (Peano.le y1 y2))) y0.
Definition term236 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 (S y2)) \/ ((~ (y1 = (S y2))) /\ (~ (Peano.le y1 y2)))) y0.
Definition term483 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term151 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term372 := imp (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term331 (x0 : nat) (x1 : nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 = (NUMERAL 0)) = y0) -> (y0 -> ((Nat.add x0 x1) = (NUMERAL 0)) = y1) -> ((x0 = (NUMERAL 0)) -> (Nat.add x0 x1) = (NUMERAL 0)) = (y0 -> y1)) x2.
Definition term145 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term288 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> y0 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 y0))).
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> (x1 = (NUMERAL 0)) -> (~ ((Nat.modulo x2 (NUMERAL (BIT1 0))) = (Nat.modulo x2 (NUMERAL 0)))) -> ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)))) -> False.
Definition term398 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term546 := fun y0 : type1606 => (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) /\ ((fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0).
Definition term106 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (Nat.modulo x0 y0) = (Nat.modulo x0 (NUMERAL 0))) (@COND nat (x1 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term311 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term467 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term561 (x0 : type1606) (x1 : nat) (x2 : nat) := (x2 = (Nat.add x1 (x0 x1 x2))) \/ (~ (Peano.le x1 x2)).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.modulo x0 (@COND nat (x1 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0))) (@COND nat (x2 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term326 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (False -> ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) = x3) -> ((~ False) -> ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2))) = x4) -> (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> (Nat.add x1 x2) = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 (Nat.add x1 x2)))) = (@COND Prop False x3 x4).
Definition term93 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.modulo x0 y0) = (Nat.modulo x0 (NUMERAL 0))) (@COND nat (x1 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term305 (x0 : nat) := False /\ (~ (x0 = (NUMERAL 0))).
Definition term278 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt (Nat.modulo x1 (Nat.pow x2 x3)) (Nat.pow x2 (Nat.add x3 x0))) -> (Nat.modulo (Nat.modulo x1 (Nat.pow x2 x3)) (Nat.pow x2 (Nat.add x3 x0))) = (Nat.modulo x1 (Nat.pow x2 x3)).
Definition term39 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term364 (x0 : nat) (x1 : nat) := ~ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term526 (x0 : type1606) := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (y1 = (Nat.add y0 (x0 y0 y1))).
Definition term421 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ ((~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term387 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ (Peano.le y0 x0)) -> (~ (exists y2 : nat, y0 = (Nat.add x0 y2))) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) = (exists y4 : nat, y3 = (Nat.add y2 y4))) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) \/ (Peano.le y3 y2)).
Definition term386 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ (Peano.le y0 x0)) -> (~ (exists y2 : nat, y0 = (Nat.add x0 y2))) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) = (exists y4 : nat, y3 = (Nat.add y2 y4))) -> (forall y2 : nat, forall y3 : nat, (Peano.le y2 y3) \/ (Peano.le y3 y2)) -> False.
Definition term227 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term226 := fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1))).
Definition term170 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ ((~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term149 := fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term134 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) -> (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (x0 = (NUMERAL 0)) -> (~ ((Nat.modulo x1 (NUMERAL (BIT1 0))) = (Nat.modulo x1 (NUMERAL 0)))) -> ~ ((forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.le y2 (S y3)) = ((y2 = (S y3)) \/ (Peano.le y2 y3)))).
Definition term133 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) -> (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (x0 = (NUMERAL 0)) -> (~ ((Nat.modulo x1 (NUMERAL (BIT1 0))) = (Nat.modulo x1 (NUMERAL 0)))) -> ((forall y2 : nat, (Peano.le y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.le y2 (S y3)) = ((y2 = (S y3)) \/ (Peano.le y2 y3)))) -> False.
Definition term259 (x0 : nat) := ~ (~ (Peano.le x0 (NUMERAL 0))).
Definition term67 := NUMERAL (BIT1 0).
Definition term379 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> (~ (exists y0 : nat, x0 = (Nat.add x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term162 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) \/ (~ ((x0 = (S x1)) \/ (Peano.le x0 x1))).
Definition term571 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add x1 x2)) -> False.
Definition term169 (x0 : nat) := forall y0 : nat, ((Peano.le x0 (S y0)) \/ ((~ (x0 = (S y0))) /\ (~ (Peano.le x0 y0)))) /\ ((~ (Peano.le x0 (S y0))) \/ ((x0 = (S y0)) \/ (Peano.le x0 y0))).
Definition term157 := forall y0 : nat, ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term550 (x0 : type1606) (x1 : nat) := fun y0 : nat => (~ (Peano.le x1 y0)) \/ (y0 = (Nat.add x1 (x0 x1 y0))).
Definition term557 (x0 : Prop) := x0 -> ~ x0.
Definition term391 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (~ (Peano.le y1 y0)) -> (~ (exists y3 : nat, y1 = (Nat.add y0 y3))) -> (forall y3 : nat, forall y4 : nat, (Peano.le y3 y4) = (exists y5 : nat, y4 = (Nat.add y3 y5))) -> ~ (forall y3 : nat, forall y4 : nat, (Peano.le y3 y4) \/ (Peano.le y4 y3)).
Definition term390 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (~ (Peano.le y1 y0)) -> (~ (exists y3 : nat, y1 = (Nat.add y0 y3))) -> (forall y3 : nat, forall y4 : nat, (Peano.le y3 y4) = (exists y5 : nat, y4 = (Nat.add y3 y5))) -> (forall y3 : nat, forall y4 : nat, (Peano.le y3 y4) \/ (Peano.le y4 y3)) -> False.
Definition term142 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (y3 = (NUMERAL 0)) -> (~ (y2 = (NUMERAL 0))) -> (Peano.le y2 y1) -> (y1 = (NUMERAL 0)) -> (~ ((Nat.modulo y0 (NUMERAL (BIT1 0))) = (Nat.modulo y0 (NUMERAL 0)))) -> ~ ((forall y4 : nat, (Peano.le y4 (NUMERAL 0)) = (y4 = (NUMERAL 0))) /\ (forall y4 : nat, forall y5 : nat, (Peano.le y4 (S y5)) = ((y4 = (S y5)) \/ (Peano.le y4 y5)))).
Definition term141 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (y3 = (NUMERAL 0)) -> (~ (y2 = (NUMERAL 0))) -> (Peano.le y2 y1) -> (y1 = (NUMERAL 0)) -> (~ ((Nat.modulo y0 (NUMERAL (BIT1 0))) = (Nat.modulo y0 (NUMERAL 0)))) -> ((forall y4 : nat, (Peano.le y4 (NUMERAL 0)) = (y4 = (NUMERAL 0))) /\ (forall y4 : nat, forall y5 : nat, (Peano.le y4 (S y5)) = ((y4 = (S y5)) \/ (Peano.le y4 y5)))) -> False.
Definition term138 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, (y2 = (NUMERAL 0)) -> (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (y0 = (NUMERAL 0)) -> (~ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (Nat.modulo x0 (NUMERAL 0)))) -> ~ ((forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (Peano.le y3 (S y4)) = ((y3 = (S y4)) \/ (Peano.le y3 y4)))).
Definition term137 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, (y2 = (NUMERAL 0)) -> (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (y0 = (NUMERAL 0)) -> (~ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (Nat.modulo x0 (NUMERAL 0)))) -> ((forall y3 : nat, (Peano.le y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (Peano.le y3 (S y4)) = ((y3 = (S y4)) \/ (Peano.le y3 y4)))) -> False.
Definition term156 := fun y0 : nat => ((Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term244 := ((forall y0 : nat, (Peano.le y0 (NUMERAL 0)) \/ (~ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (~ (Peano.le y0 (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) \/ ((~ (y0 = (S y1))) /\ (~ (Peano.le y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 (S y1))) \/ ((y0 = (S y1)) \/ (Peano.le y0 y1)))).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.lt x0 y1) /\ (Peano.le y1 y0)) -> Peano.lt x0 y0) x1.
Definition term79 (x0 : nat) (x1 : nat) := @COND nat ((@COND nat (Peano.le x0 x1) x0 x1) = (NUMERAL 0)).
Definition term293 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term19 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> (Nat.modulo x0 y0) = x0.
Definition term567 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
