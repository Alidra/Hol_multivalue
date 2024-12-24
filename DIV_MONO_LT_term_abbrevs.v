Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term129 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term265 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2.
Definition term190 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))))).
Definition term196 (x0 : nat) (x1 : nat) := (~ (Peano.le (S x0) x1)) -> Peano.le (S x0) x1.
Definition term247 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((Peano.le x1 (Nat.div x0 x3)) = x4) -> (x4 -> (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3)) = x5) -> ((Peano.le x1 (Nat.div x0 x3)) -> Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3)) = (x4 -> x5).
Definition term169 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))).
Definition term98 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0).
Definition term327 (x0 : nat -> Prop) := ~ (all x0).
Definition term208 := (~ False) -> False.
Definition term251 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.add x1 (NUMERAL (BIT1 0)))) x2.
Definition term13 (x0 : nat) (x1 : nat) := (((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False.
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term367 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((~ (Peano.le x0 x2)) \/ (~ (Peano.le x1 y0))) \/ (Peano.le (Nat.add x0 x1) (Nat.add x2 y0))) x3.
Definition term321 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term353 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.le x0 x1) /\ (Peano.le x1 x2))).
Definition term11 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False.
Definition term81 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0)).
Definition term267 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2.
Definition term90 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0).
Definition term65 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0).
Definition term218 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term142 (x0 : Prop) := ~ (~ x0).
Definition term412 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le (Nat.add y2 y1) y0) -> (~ (forall y3 : nat, (Peano.le (Nat.mul y1 y3) y2) -> Peano.le (Nat.add (Nat.mul y1 y3) y1) y0)) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, forall y6 : nat, ((Peano.le y3 y5) /\ (Peano.le y4 y6)) -> Peano.le (Nat.add y3 y4) (Nat.add y5 y6)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y3 y4) /\ (Peano.le y4 y5)) -> Peano.le y3 y5) -> (forall y3 : nat, Peano.le y3 y3) -> False) x0.
Definition term368 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2)) x0.
Definition term364 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((~ (Peano.le y0 y2)) \/ (~ (Peano.le y1 y3))) \/ (Peano.le (Nat.add y0 y1) (Nat.add y2 y3))) x0.
Definition term230 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y2 (Nat.div y1 y0)) = (Peano.le (Nat.mul y0 y2) y1)) x0.
Definition term223 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term376 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x1 x3)) \/ (Peano.le (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term55 (x0 : nat) (x1 : nat) := (forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1)) /\ (~ (Peano.lt x0 x1)).
Definition term54 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) /\ (~ (Peano.lt x0 x1)).
Definition term344 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((~ (Peano.le x0 x2)) \/ (~ (Peano.le x1 y0))) \/ (Peano.le (Nat.add x0 x1) (Nat.add x2 y0)).
Definition term286 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term257 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul x0 (Nat.add x1 (NUMERAL (BIT1 0)))).
Definition term76 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0).
Definition term390 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 x0) x1) /\ (Peano.le x2 x2).
Definition term111 (x0 : nat) := (fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) x0.
Definition term372 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2)).
Definition term385 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (Peano.le x0 x1))) /\ (~ (~ (Peano.le x2 x3))).
Definition term389 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((Peano.le x0 x1) /\ (Peano.le x2 x3)).
Definition term405 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x0 x1))) /\ (~ (~ (Peano.le x1 x2))).
Definition term187 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (Peano.le x1 x2))).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term382 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.le (Nat.add x0 x2) (Nat.add x1 x3)) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x2 x3)))).
Definition term290 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, Peano.le y0 y0).
Definition term289 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term333 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x1 y0) x0) /\ (~ (Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)).
Definition term281 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, Peano.le y0 y0).
Definition term274 := (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term122 (x0 : nat) := (~ ((S x0) = (Nat.add x0 (NUMERAL (BIT1 0))))) -> (S x0) = (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term216 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, (Peano.le y0 (Nat.div x0 x2)) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) (Nat.div x1 x2)) -> Peano.lt (Nat.div x0 x2) (Nat.div x1 x2).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term155 (x0 : nat) := ~ (x0 = x0).
Definition term249 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((Peano.le (Nat.mul x1 x2) x3) -> (Peano.le (Nat.add x2 (NUMERAL (BIT1 0))) (Nat.div x0 x1)) = x4) -> ((Peano.le x2 (Nat.div x3 x1)) -> Peano.le (Nat.add x2 (NUMERAL (BIT1 0))) (Nat.div x0 x1)) = ((Peano.le (Nat.mul x1 x2) x3) -> x4).
Definition term255 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term91 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0).
Definition term66 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0).
Definition term109 := (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)).
Definition term58 (x0 : nat) := forall y0 : nat, ((Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) /\ ((~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0)).
Definition term406 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term388 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x2 x3)))).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term359 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term334 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.le (Nat.mul x1 y0) x0) /\ (~ (Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)).
Definition term167 (x0 : nat) (x1 : nat) := (~ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1)) -> Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term175 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x3) \/ ((~ (x1 = x0)) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3)))).
Definition term41 := fun y0 : nat => Peano.le y0 y0.
Definition term414 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.add y0 x0) x1) -> (~ (forall y1 : nat, (Peano.le (Nat.mul x0 y1) y0) -> Peano.le (Nat.add (Nat.mul x0 y1) x0) x1)) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y1 y3) /\ (Peano.le y2 y4)) -> Peano.le (Nat.add y1 y2) (Nat.add y3 y4)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> (forall y1 : nat, Peano.le y1 y1) -> False) x2.
Definition term171 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (x1 = x2)).
Definition term173 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x3) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3))).
Definition term193 (x0 : nat) (x1 : nat) := (x1 = x1) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term261 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le (Nat.mul x2 x1) x0) -> (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x3 x2)) = (Peano.le (Nat.add (Nat.mul x2 x1) x2) x3)) -> ((Peano.le x1 (Nat.div x0 x2)) -> Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x3 x2)) = ((Peano.le (Nat.mul x2 x1) x0) -> Peano.le (Nat.add (Nat.mul x2 x1) x2) x3).
Definition term380 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.add x0 x2) (Nat.add x1 x3)) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x2 x3))).
Definition term17 := forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term256 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 x0) x1.
Definition term85 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0.
Definition term80 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0.
Definition term341 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((~ (Peano.le x0 x2)) \/ (~ (Peano.le x1 x3))) \/ (Peano.le (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term259 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x1 x0) x1) x2.
Definition term174 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((Peano.le x0 x3) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3)))).
Definition term135 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term63 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term337 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term145 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term415 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.div x0 x2) (Nat.div x1 x2).
Definition term21 := imp (forall y0 : nat, Peano.le y0 y0).
Definition term340 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((Peano.le x0 x2) /\ (Peano.le x1 x3))) \/ (Peano.le (Nat.add x0 x1) (Nat.add x2 x3)).
Definition term269 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2).
Definition term16 := ~ (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))).
Definition term88 := fun y0 : nat => (forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)).
Definition term221 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term183 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (Peano.le x0 x1))))) -> Peano.le x2 x3.
Definition term408 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.add (Nat.mul x2 x0) x2) (Nat.add x1 x2)) /\ (Peano.le (Nat.add x1 x2) x3).
Definition term165 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term124 (x0 : Prop) := (~ x0) -> x0.
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term200 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt x0 x1) \/ (~ (Peano.le (S x0) x1))).
Definition term194 (x0 : nat) (x1 : nat) := ((Nat.add x0 (NUMERAL (BIT1 0))) = (S x0)) /\ ((x1 = x1) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1)).
Definition term291 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term284 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, Peano.le y0 y0).
Definition term68 (x0 : nat) := fun y0 : nat => (~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0).
Definition term72 (x0 : nat) (x1 : nat) := and ((Peano.le (S x0) x1) \/ (~ (Peano.lt x0 x1))).
Definition term139 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term157 (x0 : nat) := ~ (Peano.le x0 x0).
Definition term154 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term401 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2))).
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term70 (x0 : nat) (x1 : nat) := (Peano.le (S x0) x1) \/ (~ (Peano.lt x0 x1)).
Definition term248 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((Peano.le x2 (Nat.div x3 x1)) = (Peano.le (Nat.mul x1 x2) x3)) -> ((Peano.le (Nat.mul x1 x2) x3) -> (Peano.le (Nat.add x2 (NUMERAL (BIT1 0))) (Nat.div x0 x1)) = x4) -> ((Peano.le x2 (Nat.div x3 x1)) -> Peano.le (Nat.add x2 (NUMERAL (BIT1 0))) (Nat.div x0 x1)) = ((Peano.le (Nat.mul x1 x2) x3) -> x4).
Definition term280 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term162 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x0))) -> Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) x2.
Definition term45 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1.
Definition term100 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1))).
Definition term99 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0)).
Definition term78 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) /\ ((~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0))).
Definition term77 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0) /\ ((fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0)).
Definition term402 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term134 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term396 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (Nat.add x0 x1) x2).
Definition term375 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (Nat.mul x0 x1) x2).
Definition term373 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (Nat.add (Nat.mul x1 x0) x1) x2).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term397 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (Peano.le x1 x2).
Definition term73 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0)) x1.
Definition term277 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term19 := (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False.
Definition term416 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ (Peano.le (Nat.add x0 x2) x1)) -> Peano.lt (Nat.div x0 x2) (Nat.div x1 x2).
Definition term156 (x0 : nat) := (~ (Peano.le x0 x0)) -> Peano.le x0 x0.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term413 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.add y1 y0) x0) -> (~ (forall y2 : nat, (Peano.le (Nat.mul y0 y2) y1) -> Peano.le (Nat.add (Nat.mul y0 y2) y0) x0)) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y2 y4) /\ (Peano.le y3 y5)) -> Peano.le (Nat.add y2 y3) (Nat.add y4 y5)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> (forall y2 : nat, Peano.le y2 y2) -> False) x1.
Definition term369 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1)) x1.
Definition term232 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0)) x1.
Definition term225 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul x2 x1) x0) -> Peano.le (Nat.add (Nat.mul x2 x1) x2) x3.
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.le x1 x3) \/ ((~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))))).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) x2).
Definition term392 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x2 x0) x2) (Nat.add x1 x2).
Definition term153 (x0 : nat) := ~ ((Nat.add x0 (NUMERAL (BIT1 0))) = (S x0)).
Definition term182 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term215 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term360 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term323 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term308 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term93 := fun y0 : nat => forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1).
Definition term39 := fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term191 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x2 = x0) /\ ((x3 = x1) /\ (Peano.le x2 x3))).
Definition term198 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) \/ (~ (Peano.le (S x0) x1)).
Definition term325 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((Peano.le (Nat.mul x2 x1) x0) -> Peano.le (Nat.add (Nat.mul x2 x1) x2) x3).
Definition term410 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.add (Nat.mul x1 x0) x1) x2)) -> Peano.le (Nat.add (Nat.mul x1 x0) x1) x2.
Definition term395 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.add x0 x1) x2)) -> Peano.le (Nat.add x0 x1) x2.
Definition term374 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.mul x0 x1) x2)) -> Peano.le (Nat.mul x0 x1) x2.
Definition term220 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term239 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term110 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term159 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term79 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0.
Definition term358 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term172 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term132 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term211 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1) -> Peano.lt x0 x1.
Definition term27 (x0 : nat) := fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le (Nat.add y1 (NUMERAL (BIT1 0))) x0) -> Peano.lt y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : nat, forall y2 : nat, (Peano.le (S y1) y2) = (Peano.lt y1 y2)) -> ~ (forall y1 : nat, (S y1) = (Nat.add y1 (NUMERAL (BIT1 0)))).
Definition term305 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term188 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) /\ (Peano.le x1 x2).
Definition term335 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.le x2 x3)).
Definition term296 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.add y0 x0) x1) -> (~ (forall y1 : nat, (Peano.le (Nat.mul x0 y1) y0) -> Peano.le (Nat.add (Nat.mul x0 y1) x0) x1)) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y1 y3) /\ (Peano.le y2 y4)) -> Peano.le (Nat.add y1 y2) (Nat.add y3 y4)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> ~ (forall y1 : nat, Peano.le y1 y1).
Definition term295 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.add y0 x0) x1) -> (~ (forall y1 : nat, (Peano.le (Nat.mul x0 y1) y0) -> Peano.le (Nat.add (Nat.mul x0 y1) x0) x1)) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y1 y3) /\ (Peano.le y2 y4)) -> Peano.le (Nat.add y1 y2) (Nat.add y3 y4)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> (forall y1 : nat, Peano.le y1 y1) -> False.
Definition term29 (x0 : nat) := forall y0 : nat, (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le (Nat.add y1 (NUMERAL (BIT1 0))) x0) -> Peano.lt y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : nat, forall y2 : nat, (Peano.le (S y1) y2) = (Peano.lt y1 y2)) -> ~ (forall y1 : nat, (S y1) = (Nat.add y1 (NUMERAL (BIT1 0)))).
Definition term28 (x0 : nat) := forall y0 : nat, (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le (Nat.add y1 (NUMERAL (BIT1 0))) x0) -> Peano.lt y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : nat, forall y2 : nat, (Peano.le (S y1) y2) = (Peano.lt y1 y2)) -> (forall y1 : nat, (S y1) = (Nat.add y1 (NUMERAL (BIT1 0)))) -> False.
Definition term273 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> ((~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term14 (x0 : nat) (x1 : nat) := (((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False) -> ((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False.
Definition term46 (x0 : nat) (x1 : nat) := imp (forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1).
Definition term151 (x0 : nat) := (((S x0) = (Nat.add x0 (NUMERAL (BIT1 0)))) /\ ((S x0) = (S x0))) -> (Nat.add x0 (NUMERAL (BIT1 0))) = (S x0).
Definition term83 (x0 : nat) := and (forall y0 : nat, (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))).
Definition term53 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1)).
Definition term52 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1).
Definition term214 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x0 x1) x2.
Definition term38 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term202 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le (S x0) x1)).
Definition term123 (x0 : nat) := ~ ((S x0) = (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term229 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term118 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x2 x3) = (Peano.le x0 x1)) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term355 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x1 x0) /\ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term371 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x2)) \/ ((~ (Peano.le x1 x3)) \/ (Peano.le (Nat.add x0 x1) (Nat.add x2 x3))).
Definition term74 (x0 : nat) (x1 : nat) := (~ (Peano.le (S x0) x1)) \/ (Peano.lt x0 x1).
Definition term152 (x0 : nat) := (~ ((Nat.add x0 (NUMERAL (BIT1 0))) = (S x0))) -> (Nat.add x0 (NUMERAL (BIT1 0))) = (S x0).
Definition term138 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term394 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (Nat.add (Nat.mul x2 x0) x2) (Nat.add x1 x2)).
Definition term419 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y2 = (NUMERAL 0))) /\ (Peano.le (Nat.add y0 y2) y1)) -> Peano.lt (Nat.div y0 y2) (Nat.div y1 y2).
Definition term418 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ (Peano.le (Nat.add x0 y1) y0)) -> Peano.lt (Nat.div x0 y1) (Nat.div y0 y1).
Definition term363 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term361 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term350 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((~ (Peano.le y0 y2)) \/ (~ (Peano.le y1 y3))) \/ (Peano.le (Nat.add y0 y1) (Nat.add y2 y3)).
Definition term348 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y0 y2))) \/ (Peano.le (Nat.add x0 y0) (Nat.add y1 y2)).
Definition term346 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le x1 y1))) \/ (Peano.le (Nat.add x0 x1) (Nat.add y0 y1)).
Definition term324 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term320 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term318 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2).
Definition term316 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1).
Definition term311 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term309 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term304 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le (Nat.add y2 y1) y0) -> (~ (forall y3 : nat, (Peano.le (Nat.mul y1 y3) y2) -> Peano.le (Nat.add (Nat.mul y1 y3) y1) y0)) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, forall y6 : nat, ((Peano.le y3 y5) /\ (Peano.le y4 y6)) -> Peano.le (Nat.add y3 y4) (Nat.add y5 y6)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y3 y4) /\ (Peano.le y4 y5)) -> Peano.le y3 y5) -> ~ (forall y3 : nat, Peano.le y3 y3).
Definition term303 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le (Nat.add y2 y1) y0) -> (~ (forall y3 : nat, (Peano.le (Nat.mul y1 y3) y2) -> Peano.le (Nat.add (Nat.mul y1 y3) y1) y0)) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, forall y6 : nat, ((Peano.le y3 y5) /\ (Peano.le y4 y6)) -> Peano.le (Nat.add y3 y4) (Nat.add y5 y6)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y3 y4) /\ (Peano.le y4 y5)) -> Peano.le y3 y5) -> (forall y3 : nat, Peano.le y3 y3) -> False.
Definition term300 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.add y1 y0) x0) -> (~ (forall y2 : nat, (Peano.le (Nat.mul y0 y2) y1) -> Peano.le (Nat.add (Nat.mul y0 y2) y0) x0)) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y2 y4) /\ (Peano.le y3 y5)) -> Peano.le (Nat.add y2 y3) (Nat.add y4 y5)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> ~ (forall y2 : nat, Peano.le y2 y2).
Definition term299 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.add y1 y0) x0) -> (~ (forall y2 : nat, (Peano.le (Nat.mul y0 y2) y1) -> Peano.le (Nat.add (Nat.mul y0 y2) y0) x0)) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y2 y4) /\ (Peano.le y3 y5)) -> Peano.le (Nat.add y2 y3) (Nat.add y4 y5)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> (forall y2 : nat, Peano.le y2 y2) -> False.
Definition term231 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0).
Definition term224 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term108 := forall y0 : nat, forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1).
Definition term103 := forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1)).
Definition term60 := forall y0 : nat, forall y1 : nat, ((Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ ((~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)).
Definition term40 := forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term33 := forall y0 : nat, forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le (Nat.add y2 (NUMERAL (BIT1 0))) y0) -> Peano.lt y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : nat, forall y3 : nat, (Peano.le (S y2) y3) = (Peano.lt y2 y3)) -> ~ (forall y2 : nat, (S y2) = (Nat.add y2 (NUMERAL (BIT1 0)))).
Definition term32 := forall y0 : nat, forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le (Nat.add y2 (NUMERAL (BIT1 0))) y0) -> Peano.lt y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : nat, forall y3 : nat, (Peano.le (S y2) y3) = (Peano.lt y2 y3)) -> (forall y2 : nat, (S y2) = (Nat.add y2 (NUMERAL (BIT1 0)))) -> False.
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) x1.
Definition term207 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> False.
Definition term97 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)) x0).
Definition term366 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le x1 y1))) \/ (Peano.le (Nat.add x0 x1) (Nat.add y0 y1))) x2.
Definition term365 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y0 y2))) \/ (Peano.le (Nat.add x0 y0) (Nat.add y1 y2))) x1.
Definition term381 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (Peano.le x0 x2)) \/ ((~ (Peano.le x1 x3)) \/ (Peano.le (Nat.add x0 x1) (Nat.add x2 x3)))).
Definition term205 (x0 : nat) (x1 : nat) := (Peano.le (S x0) x1) -> Peano.lt x0 x1.
Definition term67 (x0 : nat) := fun y0 : nat => (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0)).
Definition term199 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.le (S x0) x1)) \/ (Peano.lt x0 x1)).
Definition term10 (x0 : nat) (x1 : nat) := ~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1).
Definition term258 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (Nat.mul x1 x0) x1).
Definition term15 := (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term57 (x0 : nat) := fun y0 : nat => ((Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) /\ ((~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0)).
Definition term391 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le (Nat.mul x2 x0) x1) /\ (Peano.le x2 x2)) -> Peano.le (Nat.add (Nat.mul x2 x0) x2) (Nat.add x1 x2).
Definition term34 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1)) x2.
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term411 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.add (Nat.mul x1 x0) x1) x2) -> False.
Definition term271 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term336 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x1)) \/ (~ (Peano.le x2 x3)).
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x1) x2.
Definition term184 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term170 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = x0)) \/ (~ (Peano.le x1 x2)).
Definition term226 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term50 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1).
Definition term354 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term339 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := or ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x2 x3))).
Definition term283 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term331 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((fun y0 : nat => (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2) x3).
Definition term268 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> False.
Definition term288 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.le (Nat.add x0 x1) x2).
Definition term250 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 (Nat.add x1 (NUMERAL (BIT1 0)))) x2).
Definition term49 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.le y0 x0)) \/ (Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term245 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := forall y0 : Prop, ((Peano.le x1 (Nat.div x0 x3)) = x4) -> (x4 -> (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3)) = y0) -> ((Peano.le x1 (Nat.div x0 x3)) -> Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3)) = (x4 -> y0).
Definition term240 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term322 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term75 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) x1) /\ ((fun y0 : nat => (~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0)) x1).
Definition term64 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term313 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0).
Definition term125 (x0 : nat) := (~ ((S x0) = (S x0))) -> (S x0) = (S x0).
Definition term242 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, ((Peano.le x1 (Nat.div x0 x3)) = y0) -> (y0 -> (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3)) = y1) -> ((Peano.le x1 (Nat.div x0 x3)) -> Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3)) = (y0 -> y1).
Definition term241 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term407 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term386 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term144 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term219 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term307 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term22 := (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False.
Definition term378 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term253 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 (NUMERAL (BIT1 0))).
Definition term166 (x0 : nat) (x1 : nat) := (Peano.le x0 x0) -> Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term24 (x0 : nat) (x1 : nat) := imp (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)).
Definition term12 (x0 : nat) (x1 : nat) := ((~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> False.
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term113 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term343 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((~ (Peano.le x0 x2)) \/ (~ (Peano.le x1 y0))) \/ (Peano.le (Nat.add x0 x1) (Nat.add x2 y0)).
Definition term87 (x0 : nat) := (forall y0 : nat, (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) /\ (forall y0 : nat, (~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0)).
Definition term8 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1.
Definition term197 (x0 : nat) (x1 : nat) := ~ (Peano.le (S x0) x1).
Definition term192 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ ((x1 = x3) /\ (Peano.le x0 x1))) -> Peano.le x2 x3.
Definition term409 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le (Nat.add (Nat.mul x2 x1) x2) (Nat.add x0 x2)) /\ (Peano.le (Nat.add x0 x2) x3)) -> Peano.le (Nat.add (Nat.mul x2 x1) x2) x3.
Definition term326 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul x2 x1) x0) /\ (~ (Peano.le (Nat.add (Nat.mul x2 x1) x2) x3)).
Definition term246 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((Peano.le x1 (Nat.div x0 x3)) = x4) -> (x4 -> (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3)) = y0) -> ((Peano.le x1 (Nat.div x0 x3)) -> Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3)) = (x4 -> y0)) x5.
Definition term105 := and (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))).
Definition term26 (x0 : nat) := fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le (Nat.add y1 (NUMERAL (BIT1 0))) x0) -> Peano.lt y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : nat, forall y2 : nat, (Peano.le (S y1) y2) = (Peano.lt y1 y2)) -> (forall y1 : nat, (S y1) = (Nat.add y1 (NUMERAL (BIT1 0)))) -> False.
Definition term51 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term150 (x0 : nat) := ((S x0) = (Nat.add x0 (NUMERAL (BIT1 0)))) /\ ((S x0) = (S x0)).
Definition term222 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term379 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x1)) \/ ((Peano.le (Nat.add x0 x2) (Nat.add x1 x3)) \/ (~ (Peano.le x2 x3))).
Definition term106 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0.
Definition term101 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0.
Definition term209 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le (Nat.add y2 (NUMERAL (BIT1 0))) y0) -> Peano.lt y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : nat, forall y3 : nat, (Peano.le (S y2) y3) = (Peano.lt y2 y3)) -> (forall y2 : nat, (S y2) = (Nat.add y2 (NUMERAL (BIT1 0)))) -> False) x0.
Definition term96 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)) x0.
Definition term94 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) x0.
Definition term189 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) /\ ((x3 = x1) /\ (Peano.le x2 x3)).
Definition term235 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x1 (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 x1) x2).
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) x0) \/ (~ (Peano.le x1 x2)).
Definition term236 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.div x1 x2).
Definition term403 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2)))) -> Peano.le x1 x2.
Definition term400 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term383 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (Peano.le x0 x2)) \/ (~ (Peano.le x1 x3)))) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term163 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term357 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term342 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term212 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1) -> (forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1.
Definition term417 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le (Nat.add x0 y0) x1)) -> Peano.lt (Nat.div x0 y0) (Nat.div x1 y0).
Definition term314 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0).
Definition term266 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le y0 (Nat.div x0 x2)) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) (Nat.div x1 x2).
Definition term195 (x0 : nat) (x1 : nat) := (((Nat.add x0 (NUMERAL (BIT1 0))) = (S x0)) /\ ((x1 = x1) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1))) -> Peano.le (S x0) x1.
Definition term260 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul x2 x1) x0) -> (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x3 x2)) = (Peano.le (Nat.add (Nat.mul x2 x1) x2) x3).
Definition term356 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term351 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))).
Definition term176 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3))).
Definition term210 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) -> Peano.le (Nat.add y1 (NUMERAL (BIT1 0))) x0) -> Peano.lt y0 x0)) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : nat, forall y2 : nat, (Peano.le (S y1) y2) = (Peano.lt y1 y2)) -> (forall y1 : nat, (S y1) = (Nat.add y1 (NUMERAL (BIT1 0)))) -> False) x1.
Definition term404 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term384 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x2 x3))).
Definition term186 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (Peano.le x1 x2))).
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term179 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))))).
Definition term329 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.le (Nat.mul x1 y1) x0) -> Peano.le (Nat.add (Nat.mul x1 y1) x1) x2) y0).
Definition term36 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term206 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) -> Peano.lt x0 x1.
Definition term42 := forall y0 : nat, Peano.le y0 y0.
Definition term44 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1.
Definition term161 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) x0) \/ (~ (Peano.le x1 x2))).
Definition term25 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> ~ (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))).
Definition term84 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le (S x0) y1)) \/ (Peano.lt x0 y1)) y0.
Definition term278 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, Peano.le y0 y0).
Definition term20 := (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> ~ (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))).
Definition term306 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term104 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0).
Definition term82 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.le (S x0) y1) \/ (~ (Peano.lt x0 y1))) y0).
Definition term272 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term117 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term95 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) x0).
Definition term238 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) (Nat.div x1 x2).
Definition term352 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) x2.
Definition term203 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le (S x0) x1))).
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x1 (Nat.div x0 x3)) -> Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term204 (x0 : nat) (x1 : nat) := imp (Peano.le (S x0) x1).
Definition term177 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term92 := fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1)).
Definition term23 := (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) -> ~ (forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))).
Definition term213 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) /\ (Peano.le (Nat.add x0 x1) x2).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term330 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2) x3.
Definition term178 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x1 x3) \/ ((~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term89 := forall y0 : nat, (forall y1 : nat, (Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ (forall y1 : nat, (~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)).
Definition term9 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1) -> Peano.lt x0 x1)) -> False.
Definition term71 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.le (S x0) y0) \/ (~ (Peano.lt x0 y0))) x1).
Definition term332 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.le (Nat.mul x1 y1) x0) -> Peano.le (Nat.add (Nat.mul x1 y1) x1) x2) y0).
Definition term292 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, Peano.le y0 y0).
Definition term270 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.le (Nat.add x0 x1) x2) -> (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term126 (x0 : nat) := ~ ((S x0) = (S x0)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) x2)).
Definition term399 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ ((Peano.le x0 x2) \/ (~ (Peano.le x1 x2))).
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term35 := fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term37 (x0 : nat) := fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term275 := ~ (forall y0 : nat, Peano.le y0 y0).
Definition term287 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, Peano.le y0 y0).
Definition term86 (x0 : nat) := forall y0 : nat, (~ (Peano.le (S x0) y0)) \/ (Peano.lt x0 y0).
Definition term264 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le y0 (Nat.div x0 x2)) -> Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) (Nat.div x1 x2).
Definition term143 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term233 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1).
Definition term130 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Peano.le x1 (Nat.div x0 x3)) = y0) -> (y0 -> (Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3)) = y1) -> ((Peano.le x1 (Nat.div x0 x3)) -> Peano.le (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.div x2 x3)) = (y0 -> y1)) x4.
Definition term294 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.add y0 x0) x1) -> (~ (forall y1 : nat, (Peano.le (Nat.mul x0 y1) y0) -> Peano.le (Nat.add (Nat.mul x0 y1) x0) x1)) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y1 y3) /\ (Peano.le y2 y4)) -> Peano.le (Nat.add y1 y2) (Nat.add y3 y4)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> ~ (forall y1 : nat, Peano.le y1 y1).
Definition term293 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.add y0 x0) x1) -> (~ (forall y1 : nat, (Peano.le (Nat.mul x0 y1) y0) -> Peano.le (Nat.add (Nat.mul x0 y1) x0) x1)) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y1 y3) /\ (Peano.le y2 y4)) -> Peano.le (Nat.add y1 y2) (Nat.add y3 y4)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> (forall y1 : nat, Peano.le y1 y1) -> False.
Definition term201 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le (S x0) x1))) -> Peano.lt x0 x1.
Definition term107 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le (S y1) y2)) \/ (Peano.lt y1 y2)) y0.
Definition term102 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le (S y1) y2) \/ (~ (Peano.lt y1 y2))) y0.
Definition term282 := imp (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)).
Definition term279 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)).
Definition term276 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term18 := imp (forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)).
Definition term217 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term338 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := or (~ ((Peano.le x0 x1) /\ (Peano.le x2 x3))).
Definition term168 (x0 : nat) (x1 : nat) := ~ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term149 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term312 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term328 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term398 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ (~ (Peano.le x1 x2)).
Definition term252 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.add x1 (NUMERAL (BIT1 0))).
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le y0 x0)) \/ (Peano.le (Nat.add y0 (NUMERAL (BIT1 0))) x1)) x2.
Definition term370 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0)) x2.
Definition term48 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term345 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le x1 y1))) \/ (Peano.le (Nat.add x0 x1) (Nat.add y0 y1)).
Definition term315 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1).
Definition term298 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.add y1 y0) x0) -> (~ (forall y2 : nat, (Peano.le (Nat.mul y0 y2) y1) -> Peano.le (Nat.add (Nat.mul y0 y2) y0) x0)) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y2 y4) /\ (Peano.le y3 y5)) -> Peano.le (Nat.add y2 y3) (Nat.add y4 y5)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> ~ (forall y2 : nat, Peano.le y2 y2).
Definition term297 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le (Nat.add y1 y0) x0) -> (~ (forall y2 : nat, (Peano.le (Nat.mul y0 y2) y1) -> Peano.le (Nat.add (Nat.mul y0 y2) y0) x0)) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y2 y4) /\ (Peano.le y3 y5)) -> Peano.le (Nat.add y2 y3) (Nat.add y4 y5)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> (forall y2 : nat, Peano.le y2 y2) -> False.
Definition term59 := fun y0 : nat => forall y1 : nat, ((Peano.le (S y0) y1) \/ (~ (Peano.lt y0 y1))) /\ ((~ (Peano.le (S y0) y1)) \/ (Peano.lt y0 y1)).
Definition term31 := fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le (Nat.add y2 (NUMERAL (BIT1 0))) y0) -> Peano.lt y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : nat, forall y3 : nat, (Peano.le (S y2) y3) = (Peano.lt y2 y3)) -> ~ (forall y2 : nat, (S y2) = (Nat.add y2 (NUMERAL (BIT1 0)))).
Definition term30 := fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) -> Peano.le (Nat.add y2 (NUMERAL (BIT1 0))) y0) -> Peano.lt y1 y0)) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : nat, forall y3 : nat, (Peano.le (S y2) y3) = (Peano.lt y2 y3)) -> (forall y2 : nat, (S y2) = (Nat.add y2 (NUMERAL (BIT1 0)))) -> False.
Definition term387 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term254 := NUMERAL (BIT1 0).
Definition term377 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.add x0 x2) (Nat.add x1 x3)) \/ (~ (Peano.le x2 x3)).
Definition term285 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (forall y0 : nat, (Peano.le (Nat.mul x1 y0) x0) -> Peano.le (Nat.add (Nat.mul x1 y0) x1) x2)).
Definition term362 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term349 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((~ (Peano.le y0 y2)) \/ (~ (Peano.le y1 y3))) \/ (Peano.le (Nat.add y0 y1) (Nat.add y2 y3)).
Definition term347 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y0 y2))) \/ (Peano.le (Nat.add x0 y0) (Nat.add y1 y2)).
Definition term319 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term317 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2).
Definition term310 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term302 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le (Nat.add y2 y1) y0) -> (~ (forall y3 : nat, (Peano.le (Nat.mul y1 y3) y2) -> Peano.le (Nat.add (Nat.mul y1 y3) y1) y0)) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, forall y6 : nat, ((Peano.le y3 y5) /\ (Peano.le y4 y6)) -> Peano.le (Nat.add y3 y4) (Nat.add y5 y6)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y3 y4) /\ (Peano.le y4 y5)) -> Peano.le y3 y5) -> ~ (forall y3 : nat, Peano.le y3 y3).
Definition term301 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le (Nat.add y2 y1) y0) -> (~ (forall y3 : nat, (Peano.le (Nat.mul y1 y3) y2) -> Peano.le (Nat.add (Nat.mul y1 y3) y1) y0)) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, forall y6 : nat, ((Peano.le y3 y5) /\ (Peano.le y4 y6)) -> Peano.le (Nat.add y3 y4) (Nat.add y5 y6)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.le y3 y4) /\ (Peano.le y4 y5)) -> Peano.le y3 y5) -> (forall y3 : nat, Peano.le y3 y3) -> False.
Definition term393 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.add (Nat.mul x2 x0) x2) (Nat.add x1 x2))) -> Peano.le (Nat.add (Nat.mul x2 x0) x2) (Nat.add x1 x2).
Definition term56 (x0 : nat) (x1 : nat) := ((Peano.le (S x0) x1) \/ (~ (Peano.lt x0 x1))) /\ ((~ (Peano.le (S x0) x1)) \/ (Peano.lt x0 x1)).
Definition term164 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
