Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term259 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term180 (x0 : nat) (x1 : nat) := ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (x1 = (NUMERAL (BIT1 0))))).
Definition term130 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x1 y0)) x0) /\ (~ (x1 = (NUMERAL (BIT1 0)))).
Definition term248 (x0 : nat) := (fun y0 : nat => ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 x0))) (NUMERAL (BIT1 0)).
Definition term223 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0).
Definition term85 (x0 : nat -> Prop) := ~ (all x0).
Definition term294 := (~ False) -> False.
Definition term168 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x1 y0)) /\ (~ (x1 = (NUMERAL (BIT1 0))))) x0) \/ ((forall y0 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x1 y0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term267 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term6 := fun y0 : nat => (num_divides y0 (NUMERAL (BIT1 0))) = (y0 = (NUMERAL (BIT1 0))).
Definition term166 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) x1).
Definition term215 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0).
Definition term193 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0).
Definition term182 (x0 : nat) (x1 : nat) := and (((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (x1 = (NUMERAL (BIT1 0)))))).
Definition term52 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term60 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term273 (x0 : Prop) := ~ (~ x0).
Definition term197 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) x1.
Definition term181 (x0 : nat) (x1 : nat) := and (((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ (~ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))))).
Definition term201 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0).
Definition term287 (x0 : nat) (x1 : nat) := (~ (~ ((Nat.mul x1 x0) = (NUMERAL (BIT1 0))))) -> x1 = (NUMERAL (BIT1 0)).
Definition term249 (x0 : nat) := ~ ((NUMERAL (BIT1 0)) = (Nat.mul (NUMERAL (BIT1 0)) x0)).
Definition term62 := (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))))).
Definition term74 (x0 : nat) := ~ (x0 = (NUMERAL (BIT1 0))).
Definition term173 := fun y0 : nat => exists y1 : nat, (((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ ((forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y2))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term75 (x0 : nat) := and (~ (exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0))).
Definition term148 (x0 : nat) := or (exists y0 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))).
Definition term112 := or (exists y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))).
Definition term272 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term152 := fun y0 : nat => (exists y1 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ ((forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term116 := (exists y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (exists y0 : nat, (forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term281 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT1 0)) = (Nat.mul x0 x1)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL (BIT1 0))).
Definition term149 (x0 : nat) := ((fun y0 : nat => exists y1 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) x0) \/ ((fun y0 : nat => (forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0)))) x0).
Definition term13 := (~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False.
Definition term177 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term32 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term10 (x0 : Prop) := (~ x0) -> False.
Definition term216 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0).
Definition term194 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0).
Definition term234 := (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ (forall y0 : nat, forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term42 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term154 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term278 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term20 := imp ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))).
Definition term49 := fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term167 (x0 : nat) (x1 : nat) := or (((NUMERAL (BIT1 0)) = (Nat.mul x1 x0)) /\ (~ (x1 = (NUMERAL (BIT1 0))))).
Definition term242 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (x0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0))))) x1.
Definition term210 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term205 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0.
Definition term63 (x0 : nat) := fun y0 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y0).
Definition term172 (x0 : nat) := exists y0 : nat, (((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ ((forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term92 := exists y0 : nat, ((exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ ((forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term304 (x0 : nat) := ((NUMERAL (BIT1 0)) = (Nat.mul (NUMERAL (BIT1 0)) x0)) -> False.
Definition term266 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term191 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term276 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term12 := ~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0)))).
Definition term2 (x0 : nat) := exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0).
Definition term213 := fun y0 : nat => (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ (forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term18 := ~ (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term243 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term159 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) y0) \/ ((forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term156 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) \/ x1.
Definition term76 (x0 : nat) := and (forall y0 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0))).
Definition term301 := (((Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) = (NUMERAL (BIT1 0))) /\ ((Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) = (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))))) -> (NUMERAL (BIT1 0)) = (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term254 (x0 : Prop) := (~ x0) -> x0.
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term283 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) -> (Nat.mul x0 x1) = (NUMERAL (BIT1 0)).
Definition term70 (x0 : nat) (x1 : nat) := ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 x1)).
Definition term268 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term270 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term135 := fun y0 : nat => exists y1 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0)))).
Definition term264 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term141 (x0 : nat) := (fun y0 : nat => exists y1 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) x0.
Definition term131 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT1 0)) = (Nat.mul x1 x0)) /\ (~ (x1 = (NUMERAL (BIT1 0)))).
Definition term125 (x0 : nat) := and (exists y0 : nat, (fun y1 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) y0).
Definition term133 (x0 : nat) := fun y0 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term225 := @eq Prop (forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ (forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))))).
Definition term224 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0)).
Definition term203 (x0 : nat) := @eq Prop (forall y0 : nat, (((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))))).
Definition term202 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0) /\ ((fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0)).
Definition term265 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term7 := fun y0 : nat => (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))).
Definition term178 (x0 : nat) (x1 : nat) := or ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))).
Definition term190 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term44 := fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term142 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term1 (x0 : nat) := num_divides x0 (NUMERAL (BIT1 0)).
Definition term247 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 x0))) x1.
Definition term262 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term138 := (exists y0 : nat, exists y1 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (exists y0 : nat, (forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term104 (x0 : nat) := ((fun y0 : nat => (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) x0) \/ ((fun y0 : nat => (forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0)))) x0).
Definition term27 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term25 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))).
Definition term35 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term245 (x0 : nat) (x1 : nat) := (~ ((Nat.mul x1 x0) = (NUMERAL (BIT1 0)))) \/ (x1 = (NUMERAL (BIT1 0))).
Definition term39 := fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term110 := exists y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0)))).
Definition term29 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term122 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) y0) /\ (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term84 (x0 : nat) := ~ ((exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) = (x0 = (NUMERAL (BIT1 0)))).
Definition term4 (x0 : nat) := @eq Prop (num_divides x0 (NUMERAL (BIT1 0))).
Definition term107 := @eq Prop (exists y0 : nat, ((exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ ((forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term106 := @eq Prop (exists y0 : nat, ((fun y1 : nat => (exists y2 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0)).
Definition term5 (x0 : nat) := @eq Prop (exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)).
Definition term244 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0))) x1.
Definition term9 := forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))).
Definition term89 (x0 : nat) := ~ ((fun y0 : nat => (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0)))) x0).
Definition term298 := (~ ((Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) = (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))))) -> (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) = (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term45 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term256 := ~ ((NUMERAL (BIT1 0)) = (NUMERAL (BIT1 0))).
Definition term252 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term284 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))).
Definition term82 (x0 : nat) := ((exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ ((~ (exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term196 (x0 : nat) := fun y0 : nat => (~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term139 := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term98 := (exists y0 : nat, (fun y1 : nat => (exists y2 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term17 := (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False.
Definition term83 (x0 : nat) := ((exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ ((forall y0 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term165 (x0 : nat) := @eq Prop ((exists y0 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ ((forall y0 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0))) /\ (x0 = (NUMERAL (BIT1 0))))).
Definition term164 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) y0) \/ ((forall y0 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0))) /\ (x0 = (NUMERAL (BIT1 0))))).
Definition term295 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term88 (x0 : nat) := (fun y0 : nat => (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0)))) x0.
Definition term161 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) y0.
Definition term108 := fun y0 : nat => (fun y1 : nat => (exists y2 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term282 (x0 : nat) (x1 : nat) := (((NUMERAL (BIT1 0)) = (Nat.mul x0 x1)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL (BIT1 0)))) -> (Nat.mul x0 x1) = (NUMERAL (BIT1 0)).
Definition term208 (x0 : nat) := and (forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))).
Definition term61 := and (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)).
Definition term56 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term73 (x0 : nat) := forall y0 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)).
Definition term0 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul x1 y0).
Definition term100 := fun y0 : nat => (forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0))).
Definition term14 := ((~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False) -> (~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False.
Definition term209 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ ((Nat.mul x0 y1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term204 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0.
Definition term290 (x0 : nat) (x1 : nat) := imp ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))).
Definition term51 := and (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0).
Definition term46 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0).
Definition term184 (x0 : nat) (x1 : nat) := (((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (x1 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))))).
Definition term211 (x0 : nat) := forall y0 : nat, (~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term269 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term240 := forall y0 : nat, forall y1 : nat, ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y1 = (NUMERAL (BIT1 0)))).
Definition term233 := forall y0 : nat, forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term228 := forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0))))).
Definition term188 := forall y0 : nat, forall y1 : nat, (((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term40 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term34 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term19 := forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term302 := (~ ((NUMERAL (BIT1 0)) = (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))))) -> (NUMERAL (BIT1 0)) = (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term160 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) x1.
Definition term8 := forall y0 : nat, (num_divides y0 (NUMERAL (BIT1 0))) = (y0 = (NUMERAL (BIT1 0))).
Definition term80 (x0 : nat) := (exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term222 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) x0).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term176 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (x1 = (NUMERAL (BIT1 0)))).
Definition term64 (x0 : nat -> Prop) := ~ (ex x0).
Definition term140 := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term97 := exists y0 : nat, ((fun y1 : nat => (exists y2 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term289 (x0 : nat) (x1 : nat) := imp (~ (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))))).
Definition term183 (x0 : nat) (x1 : nat) := (((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ (~ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))))).
Definition term65 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term50 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term26 (x0 : nat) := fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term258 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term38 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term137 := or (exists y0 : nat, exists y1 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))).
Definition term132 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) y0) /\ (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term120 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term11 := (~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> False.
Definition term237 (x0 : nat) := fun y0 : nat => ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (x0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0)))).
Definition term102 (x0 : nat) := or ((fun y0 : nat => (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) x0).
Definition term77 (x0 : nat) := (~ (exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0))) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term200 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) x1) /\ ((fun y0 : nat => (~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x1).
Definition term192 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term134 (x0 : nat) := exists y0 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term171 (x0 : nat) := fun y0 : nat => (((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ ((forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term261 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term195 (x0 : nat) := fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0))))).
Definition term170 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) y0) \/ ((forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term162 (x0 : nat) := exists y0 : nat, (fun y1 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) y0.
Definition term124 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) y0.
Definition term114 := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0.
Definition term109 := exists y0 : nat, (fun y1 : nat => (exists y2 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term297 := ~ ((Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) = (NUMERAL (BIT1 0))).
Definition term16 := (((~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False) -> (~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False) -> ((~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False) -> (~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False.
Definition term54 := fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term235 (x0 : nat) (x1 : nat) := ((~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ (x0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))) \/ (x1 = (NUMERAL (BIT1 0)))).
Definition term275 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term47 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term37 (x0 : nat) := fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term169 (x0 : nat) (x1 : nat) := (((NUMERAL (BIT1 0)) = (Nat.mul x1 x0)) /\ (~ (x1 = (NUMERAL (BIT1 0))))) \/ ((forall y0 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x1 y0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term288 (x0 : nat) (x1 : nat) := ~ (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0)))).
Definition term293 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) -> False.
Definition term99 := fun y0 : nat => (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0)))).
Definition term24 := (~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> ~ (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term81 (x0 : nat) := or ((exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))).
Definition term212 (x0 : nat) := (forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) /\ (forall y0 : nat, (~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term101 (x0 : nat) := (fun y0 : nat => (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) x0.
Definition term250 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 x0))) x1).
Definition term230 := and (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))).
Definition term41 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)).
Definition term119 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term255 := (~ ((NUMERAL (BIT1 0)) = (NUMERAL (BIT1 0)))) -> (NUMERAL (BIT1 0)) = (NUMERAL (BIT1 0)).
Definition term206 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0))))).
Definition term175 (x0 : nat) (x1 : nat) := ~ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term43 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term147 (x0 : nat) := or ((fun y0 : nat => exists y1 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) x0).
Definition term67 (x0 : nat) := forall y0 : nat, ~ ((fun y1 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) y0).
Definition term231 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0.
Definition term226 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0.
Definition term241 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y1 = (NUMERAL (BIT1 0))))) x0.
Definition term221 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) x0.
Definition term219 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) x0.
Definition term55 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term127 (x0 : nat) := @eq Prop ((exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))).
Definition term126 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) y0) /\ (~ (x0 = (NUMERAL (BIT1 0))))).
Definition term303 := ~ ((NUMERAL (BIT1 0)) = (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term253 (x0 : nat) (x1 : nat) := (~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 x1))) -> (NUMERAL (BIT1 0)) = (Nat.mul x0 x1).
Definition term158 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) y0) \/ ((forall y0 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term36 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term79 (x0 : nat) := and (exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)).
Definition term236 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))).
Definition term30 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term53 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term68 (x0 : nat) (x1 : nat) := (fun y0 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) x1.
Definition term185 (x0 : nat) := fun y0 : nat => (((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term153 := exists y0 : nat, (exists y1 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ ((forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term271 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term87 := exists y0 : nat, ~ ((fun y1 : nat => (exists y2 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) = (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term113 := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0.
Definition term229 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0).
Definition term207 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => ((Nat.mul x0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) y0).
Definition term220 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) x0).
Definition term299 := ~ ((Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) = (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term300 := ((Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) = (NUMERAL (BIT1 0))) /\ ((Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) = (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term21 := ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False.
Definition term179 (x0 : nat) (x1 : nat) := ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))) \/ (~ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))))).
Definition term286 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (NUMERAL (BIT1 0))) \/ (~ ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))))).
Definition term251 (x0 : nat) (x1 : nat) := @eq Prop (~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 x1))).
Definition term291 (x0 : nat) (x1 : nat) := ((Nat.mul x1 x0) = (NUMERAL (BIT1 0))) -> x1 = (NUMERAL (BIT1 0)).
Definition term123 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) y0.
Definition term72 (x0 : nat) := fun y0 : nat => ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)).
Definition term78 (x0 : nat) := (forall y0 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0))) /\ (x0 = (NUMERAL (BIT1 0))).
Definition term279 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term143 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0.
Definition term174 := exists y0 : nat, exists y1 : nat, (((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ ((forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y2))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term136 := exists y0 : nat, exists y1 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0)))).
Definition term214 := forall y0 : nat, (forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ (forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term95 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term91 := fun y0 : nat => ((exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ ((forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term58 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term198 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) x1).
Definition term128 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) x1).
Definition term90 := fun y0 : nat => ~ ((fun y1 : nat => (exists y2 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) = (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term71 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) y0).
Definition term69 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) x1).
Definition term129 (x0 : nat) (x1 : nat) := and ((NUMERAL (BIT1 0)) = (Nat.mul x0 x1)).
Definition term103 (x0 : nat) := (fun y0 : nat => (forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0)))) x0.
Definition term22 := ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> ~ (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term257 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term151 := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term105 := fun y0 : nat => ((fun y1 : nat => (exists y2 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0).
Definition term163 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => ((NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) y0).
Definition term144 := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0).
Definition term111 := or (exists y0 : nat, (fun y1 : nat => (exists y2 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0).
Definition term115 := exists y0 : nat, (forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0))).
Definition term31 (x0 : nat) := fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term292 (x0 : nat) := (~ (x0 = (NUMERAL (BIT1 0)))) -> x0 = (NUMERAL (BIT1 0)).
Definition term274 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term260 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term232 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.mul y1 y2) = (NUMERAL (BIT1 0)))) \/ ((y1 = (NUMERAL (BIT1 0))) /\ (y2 = (NUMERAL (BIT1 0))))) y0.
Definition term227 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.mul y1 y2) = (NUMERAL (BIT1 0))) \/ ((~ (y1 = (NUMERAL (BIT1 0)))) \/ (~ (y2 = (NUMERAL (BIT1 0)))))) y0.
Definition term57 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term280 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term86 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term285 (x0 : nat) (x1 : nat) := @eq Prop ((~ ((Nat.mul x1 x0) = (NUMERAL (BIT1 0)))) \/ (x1 = (NUMERAL (BIT1 0)))).
Definition term150 (x0 : nat) := (exists y0 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0)) /\ (~ (x0 = (NUMERAL (BIT1 0))))) \/ ((forall y0 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul x0 y0))) /\ (x0 = (NUMERAL (BIT1 0)))).
Definition term199 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x1.
Definition term66 (x0 : nat) := ~ (exists y0 : nat, (NUMERAL (BIT1 0)) = (Nat.mul x0 y0)).
Definition term239 := fun y0 : nat => forall y1 : nat, ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ (y1 = (NUMERAL (BIT1 0)))).
Definition term218 := fun y0 : nat => forall y1 : nat, (~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term217 := fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0))))).
Definition term187 := fun y0 : nat => forall y1 : nat, (((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) \/ ((~ (y0 = (NUMERAL (BIT1 0)))) \/ (~ (y1 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul y0 y1) = (NUMERAL (BIT1 0)))) \/ ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))).
Definition term33 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term28 := fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0)))).
Definition term3 := NUMERAL (BIT1 0).
Definition term48 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term96 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term246 (x0 : nat) := fun y0 : nat => ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 x0)).
Definition term157 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) \/ x1.
Definition term238 (x0 : nat) := forall y0 : nat, ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (x0 = (NUMERAL (BIT1 0)))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ (y0 = (NUMERAL (BIT1 0)))).
Definition term186 (x0 : nat) := forall y0 : nat, (((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) \/ (~ (y0 = (NUMERAL (BIT1 0)))))) /\ ((~ ((Nat.mul x0 y0) = (NUMERAL (BIT1 0)))) \/ ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term23 := imp (~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))).
Definition term305 := ((NUMERAL (BIT1 0)) = (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))) -> False.
Definition term296 := (~ ((Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) = (NUMERAL (BIT1 0)))) -> (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) = (NUMERAL (BIT1 0)).
Definition term59 := fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term121 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => (NUMERAL (BIT1 0)) = (Nat.mul x0 y1)) y0) /\ (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term15 := (((~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False) -> (~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False) -> (~ (forall y0 : nat, (exists y1 : nat, (NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) = (y0 = (NUMERAL (BIT1 0))))) -> ((forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) -> False.
Definition term146 := @eq Prop ((exists y0 : nat, exists y1 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1)) /\ (~ (y0 = (NUMERAL (BIT1 0))))) \/ (exists y0 : nat, (forall y1 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y0 y1))) /\ (y0 = (NUMERAL (BIT1 0))))).
Definition term145 := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2)) /\ (~ (y1 = (NUMERAL (BIT1 0))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, ~ ((NUMERAL (BIT1 0)) = (Nat.mul y1 y2))) /\ (y1 = (NUMERAL (BIT1 0)))) y0)).
