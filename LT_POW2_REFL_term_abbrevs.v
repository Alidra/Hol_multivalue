Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term49 (x0 : nat) := ((fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) x0) -> (fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) (S x0).
Definition term195 (x0 : nat) (x1 : nat) := (~ ((Nat.pow x0 x1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))).
Definition term164 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term241 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) \/ (y2 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.pow y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0).
Definition term286 := (~ False) -> False.
Definition term103 (x0 : nat) := (((~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False) -> (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False) -> (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False.
Definition term82 (x0 : nat) := Peano.lt (Nat.add x0 (S (NUMERAL 0))) (Nat.add (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term233 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) \/ (y2 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.pow y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0).
Definition term211 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ ((Nat.pow x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0).
Definition term167 := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term276 (x0 : Prop) := ~ (~ x0).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term50 (x0 : nat) := (Peano.lt x0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)) -> Peano.lt (S x0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (S x0)).
Definition term197 (x0 : nat) (x1 : nat) := ((Nat.pow x0 x1) = (NUMERAL 0)) \/ (~ ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))))).
Definition term73 (x0 : nat) := Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) /\ (Peano.le x2 x3).
Definition term219 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ ((Nat.pow x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0).
Definition term22 (x0 : nat) := (fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) x0.
Definition term190 := (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ ((forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0)))))))).
Definition term151 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))))).
Definition term40 := Peano.lt (NUMERAL 0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0)).
Definition term12 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term269 (x0 : nat) := (~ ((Nat.pow (S (NUMERAL (BIT1 0))) x0) = (NUMERAL 0))) -> (Nat.pow (S (NUMERAL (BIT1 0))) x0) = (NUMERAL 0).
Definition term159 (x0 : nat) := (~ (~ (x0 = (NUMERAL 0)))) \/ (Peano.lt (NUMERAL 0) x0).
Definition term215 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) x1.
Definition term282 := (~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) -> (S (NUMERAL (BIT1 0))) = (NUMERAL 0).
Definition term217 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term75 := S (NUMERAL 0).
Definition term28 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term98 (x0 : Prop) := (~ x0) -> False.
Definition term234 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) \/ (y2 = (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.pow y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0).
Definition term212 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ ((Nat.pow x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0).
Definition term252 := (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) /\ (forall y0 : nat, forall y1 : nat, (~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term202 (x0 : nat) (x1 : nat) := (((Nat.pow x0 x1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0)))) /\ ((~ ((Nat.pow x0 x1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))))).
Definition term100 (x0 : nat) := ~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0)).
Definition term192 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ (~ (~ (x1 = (NUMERAL 0)))).
Definition term108 := imp ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))).
Definition term228 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ ((Nat.pow x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term223 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) y0.
Definition term60 := forall y0 : nat, (fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) y0.
Definition term71 (x0 : nat) := Peano.lt (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term55 := ((fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) (S y0)).
Definition term263 (x0 : nat) (x1 : nat) := (~ ((Nat.pow x1 x0) = (NUMERAL 0))) \/ (x1 = (NUMERAL 0)).
Definition term266 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term209 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term88 (x0 : nat) := and (Peano.lt x0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term193 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0)).
Definition term231 := fun y0 : nat => (forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) /\ (forall y1 : nat, (~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term106 := ~ (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term30 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term149 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term144 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term271 (x0 : Prop) := (~ x0) -> x0.
Definition term37 := (((fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) y0.
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term19 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term287 (x0 : nat) := (fun y0 : nat => (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) y0))) -> (forall y1 : nat, ~ ((S y1) = (NUMERAL 0))) -> ((forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) /\ ((forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y1) /\ ((forall y1 : nat, (Peano.lt (NUMERAL 0) y1) -> ~ (y1 = (NUMERAL 0))) /\ ((forall y1 : nat, (Peano.lt (NUMERAL 0) y1) -> Peano.le (NUMERAL (BIT1 0)) y1) /\ ((forall y1 : nat, (Peano.le (NUMERAL (BIT1 0)) y1) -> Peano.lt (NUMERAL 0) y1) /\ (forall y1 : nat, (Peano.le (NUMERAL (BIT1 0)) y1) -> ~ (y1 = (NUMERAL 0)))))))) -> (forall y1 : nat, forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) -> False) x0.
Definition term274 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (~ ((Nat.pow x0 x1) = (NUMERAL 0)))).
Definition term128 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term34 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term36 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term66 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term74 (x0 : nat) := Peano.lt (Nat.add x0 (NUMERAL (BIT1 0))) (Nat.add (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term285 := ((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) -> False.
Definition term243 := @eq Prop (forall y0 : nat, (forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) /\ (forall y1 : nat, (~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))))).
Definition term242 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) \/ (y2 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.pow y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0)).
Definition term221 (x0 : nat) := @eq Prop (forall y0 : nat, (((Nat.pow x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) /\ ((~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))))).
Definition term220 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) y0) /\ ((fun y1 : nat => (~ ((Nat.pow x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0)).
Definition term214 (x0 : nat) := fun y0 : nat => (~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term57 := imp (((fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) (S y0))).
Definition term229 (x0 : nat) := forall y0 : nat, (~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term178 (x0 : nat) := (~ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term169 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term208 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term97 (x0 : nat) := True /\ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0)).
Definition term148 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term267 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) -> x0 = (NUMERAL 0).
Definition term162 := fun y0 : nat => (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term213 (x0 : nat) := fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term63 := Nat.pow (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0).
Definition term53 := forall y0 : nat, ((fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) (S y0).
Definition term121 (x0 : nat) := fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term161 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term18 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term48 (x0 : nat) := Peano.lt (S x0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (S x0)).
Definition term93 := Nat.pow (S (NUMERAL (BIT1 0))).
Definition term81 (x0 : nat) := Peano.lt (Nat.add x0 (S (NUMERAL 0))).
Definition term203 (x0 : nat) := fun y0 : nat => (((Nat.pow x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) /\ ((~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))).
Definition term94 (x0 : nat) := Nat.pow (S (NUMERAL (BIT1 0))) x0.
Definition term154 := forall y0 : nat, ~ ((S y0) = (NUMERAL 0)).
Definition term41 := and ((fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) (NUMERAL 0)).
Definition term47 (x0 : nat) := (fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) (S x0).
Definition term46 (x0 : nat) := imp (Peano.lt x0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term255 (x0 : nat) := fun y0 : nat => ((~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ (x0 = (NUMERAL 0))) /\ ((~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ (~ (y0 = (NUMERAL 0)))).
Definition term117 := fun y0 : nat => (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) y0))) -> (forall y1 : nat, ~ ((S y1) = (NUMERAL 0))) -> ((forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) /\ ((forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y1) /\ ((forall y1 : nat, (Peano.lt (NUMERAL 0) y1) -> ~ (y1 = (NUMERAL 0))) /\ ((forall y1 : nat, (Peano.lt (NUMERAL 0) y1) -> Peano.le (NUMERAL (BIT1 0)) y1) /\ ((forall y1 : nat, (Peano.le (NUMERAL (BIT1 0)) y1) -> Peano.lt (NUMERAL 0) y1) /\ (forall y1 : nat, (Peano.le (NUMERAL (BIT1 0)) y1) -> ~ (y1 = (NUMERAL 0)))))))) -> ~ (forall y1 : nat, forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))).
Definition term25 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term42 := and (Peano.lt (NUMERAL 0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0))).
Definition term120 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))).
Definition term105 := (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False.
Definition term101 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False.
Definition term119 := forall y0 : nat, (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) y0))) -> (forall y1 : nat, ~ ((S y1) = (NUMERAL 0))) -> ((forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) /\ ((forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y1) /\ ((forall y1 : nat, (Peano.lt (NUMERAL 0) y1) -> ~ (y1 = (NUMERAL 0))) /\ ((forall y1 : nat, (Peano.lt (NUMERAL 0) y1) -> Peano.le (NUMERAL (BIT1 0)) y1) /\ ((forall y1 : nat, (Peano.le (NUMERAL (BIT1 0)) y1) -> Peano.lt (NUMERAL 0) y1) /\ (forall y1 : nat, (Peano.le (NUMERAL (BIT1 0)) y1) -> ~ (y1 = (NUMERAL 0)))))))) -> ~ (forall y1 : nat, forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))).
Definition term118 := forall y0 : nat, (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) y0))) -> (forall y1 : nat, ~ ((S y1) = (NUMERAL 0))) -> ((forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) /\ ((forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y1) /\ ((forall y1 : nat, (Peano.lt (NUMERAL 0) y1) -> ~ (y1 = (NUMERAL 0))) /\ ((forall y1 : nat, (Peano.lt (NUMERAL 0) y1) -> Peano.le (NUMERAL (BIT1 0)) y1) /\ ((forall y1 : nat, (Peano.le (NUMERAL (BIT1 0)) y1) -> Peano.lt (NUMERAL 0) y1) /\ (forall y1 : nat, (Peano.le (NUMERAL (BIT1 0)) y1) -> ~ (y1 = (NUMERAL 0)))))))) -> (forall y1 : nat, forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) -> False.
Definition term20 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term160 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) x0).
Definition term89 (x0 : nat) := Peano.le (S (NUMERAL 0)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term104 (x0 : nat) := (((~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False) -> (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False) -> ((~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False) -> (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False.
Definition term226 (x0 : nat) := and (forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))).
Definition term189 := and (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0)).
Definition term187 := and (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)).
Definition term185 := and (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term183 := and (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)).
Definition term181 := and (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)).
Definition term150 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0).
Definition term145 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term140 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term135 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term130 := and (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0).
Definition term111 := imp (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term79 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term85 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term76 := Peano.lt (NUMERAL 0) (S (NUMERAL 0)).
Definition term33 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term51 := fun y0 : nat => ((fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) y0) -> (fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) (S y0).
Definition term24 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) x0.
Definition term184 := (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))))).
Definition term136 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))).
Definition term86 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) x1.
Definition term143 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term157 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term262 (x0 : nat) := (fun y0 : nat => (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0)) x0.
Definition term113 := (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> ~ (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term227 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ ((Nat.pow x0 y1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term222 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) y0.
Definition term158 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term196 (x0 : nat) (x1 : nat) := or ((Nat.pow x0 x1) = (NUMERAL 0)).
Definition term258 := forall y0 : nat, forall y1 : nat, ((~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) /\ ((~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ (~ (y1 = (NUMERAL 0)))).
Definition term251 := forall y0 : nat, forall y1 : nat, (~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term246 := forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0))).
Definition term206 := forall y0 : nat, forall y1 : nat, (((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) /\ ((~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term107 := forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term26 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term13 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.le y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term153 := fun y0 : nat => ~ ((S y0) = (NUMERAL 0)).
Definition term56 := (Peano.lt (NUMERAL 0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0))) /\ (forall y0 : nat, (Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) -> Peano.lt (S y0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (S y0))).
Definition term201 (x0 : nat) (x1 : nat) := (((Nat.pow x0 x1) = (NUMERAL 0)) \/ (~ ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))))) /\ ((~ ((Nat.pow x0 x1) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))))).
Definition term240 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0).
Definition term173 := fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.le y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term65 := Peano.lt (NUMERAL 0).
Definition term80 (x0 : nat) := Nat.add x0 (S (NUMERAL 0)).
Definition term17 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term67 (x0 : nat) := Nat.pow (NUMERAL (BIT0 (BIT1 0))) (S x0).
Definition term91 := S (NUMERAL (BIT1 0)).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.lt x0 x2) /\ (Peano.le x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term38 := fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term198 (x0 : nat) (x1 : nat) := ((Nat.pow x0 x1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0))).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x0 x2) /\ (Peano.le x1 x3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term166 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term31 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term96 (x0 : nat) := (Peano.lt x0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)) /\ (Peano.le (S (NUMERAL 0)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term268 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (Nat.pow (S (NUMERAL (BIT1 0))) x0) = (NUMERAL 0).
Definition term23 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term114 (x0 : nat) := imp (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))).
Definition term44 (x0 : nat) := Peano.lt x0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term138 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term194 (x0 : nat) (x1 : nat) := ~ ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))).
Definition term15 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term273 (x0 : nat) (x1 : nat) := @eq Prop ((~ ((Nat.pow x1 x0) = (NUMERAL 0))) \/ (x1 = (NUMERAL 0))).
Definition term191 (x0 : nat) := or (~ (x0 = (NUMERAL 0))).
Definition term152 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term277 (x0 : nat) (x1 : nat) := ~ (~ ((Nat.pow x0 x1) = (NUMERAL 0))).
Definition term147 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) x0.
Definition term199 (x0 : nat) (x1 : nat) := and (((Nat.pow x0 x1) = (NUMERAL 0)) \/ (~ ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))))).
Definition term43 (x0 : nat) := (fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) x0.
Definition term133 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term218 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) x1) /\ ((fun y0 : nat => (~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1).
Definition term210 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term180 := forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term171 := forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term168 := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term163 := forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term272 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ (~ ((Nat.pow x0 x1) = (NUMERAL 0))).
Definition term64 := NUMERAL (BIT0 (BIT1 0)).
Definition term52 := fun y0 : nat => (Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) -> Peano.lt (S y0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (S y0)).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term102 (x0 : nat) := ((~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False) -> (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False.
Definition term230 (x0 : nat) := (forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) /\ (forall y0 : nat, (~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))).
Definition term182 := (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term131 := (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term77 := ((NUMERAL 0) = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term139 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term126 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term21 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term248 := and (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))).
Definition term116 := fun y0 : nat => (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) y0))) -> (forall y1 : nat, ~ ((S y1) = (NUMERAL 0))) -> ((forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y1) /\ ((forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y1) /\ ((forall y1 : nat, (Peano.lt (NUMERAL 0) y1) -> ~ (y1 = (NUMERAL 0))) /\ ((forall y1 : nat, (Peano.lt (NUMERAL 0) y1) -> Peano.le (NUMERAL (BIT1 0)) y1) /\ ((forall y1 : nat, (Peano.le (NUMERAL (BIT1 0)) y1) -> Peano.lt (NUMERAL 0) y1) /\ (forall y1 : nat, (Peano.le (NUMERAL (BIT1 0)) y1) -> ~ (y1 = (NUMERAL 0)))))))) -> (forall y1 : nat, forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) = ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) -> False.
Definition term270 (x0 : nat) := ~ ((Nat.pow (S (NUMERAL (BIT1 0))) x0) = (NUMERAL 0)).
Definition term253 (x0 : nat) (x1 : nat) := ((~ ((Nat.pow x0 x1) = (NUMERAL 0))) \/ (x0 = (NUMERAL 0))) /\ ((~ ((Nat.pow x0 x1) = (NUMERAL 0))) \/ (~ (x1 = (NUMERAL 0)))).
Definition term224 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term249 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ ((Nat.pow y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0.
Definition term244 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) \/ (y2 = (NUMERAL 0)))) y0.
Definition term68 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term260 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) /\ ((~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ (~ (y1 = (NUMERAL 0))))) x0.
Definition term239 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term237 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) x0.
Definition term84 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) x0.
Definition term27 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term115 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> ~ (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term259 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term32 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term200 (x0 : nat) (x1 : nat) := and (((Nat.pow x0 x1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0)))).
Definition term186 := (forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0)))))).
Definition term141 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.lt x0 x2) /\ (Peano.le x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term134 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term129 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term92 := Nat.pow (NUMERAL (BIT0 (BIT1 0))).
Definition term165 (x0 : nat) := (~ (~ (x0 = (NUMERAL 0)))) \/ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term175 (x0 : nat) := (~ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.lt (NUMERAL 0) x0).
Definition term87 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term69 (x0 : nat) := Peano.lt (S x0).
Definition term279 (x0 : nat) (x1 : nat) := imp ((Nat.pow x0 x1) = (NUMERAL 0)).
Definition term261 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ (x0 = (NUMERAL 0))) /\ ((~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ (~ (y0 = (NUMERAL 0))))) x1.
Definition term72 (x0 : nat) := Nat.add (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term280 (x0 : nat) (x1 : nat) := ((Nat.pow x1 x0) = (NUMERAL 0)) -> x1 = (NUMERAL 0).
Definition term247 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) \/ (y2 = (NUMERAL 0)))) y0).
Definition term225 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => ((Nat.pow x0 y1) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) y0).
Definition term112 := (forall y0 : nat, ~ ((S y0) = (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False.
Definition term238 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) x0).
Definition term256 (x0 : nat) := forall y0 : nat, ((~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ (x0 = (NUMERAL 0))) /\ ((~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ (~ (y0 = (NUMERAL 0)))).
Definition term83 (x0 : nat) := ((Peano.lt x0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)) /\ (Peano.le (S (NUMERAL 0)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0))) -> Peano.lt (Nat.add x0 (S (NUMERAL 0))) (Nat.add (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term127 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> Peano.lt (NUMERAL 0) x0.
Definition term109 := ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) -> False.
Definition term58 := imp ((Peano.lt (NUMERAL 0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0))) /\ (forall y0 : nat, (Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) -> Peano.lt (S y0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (S y0)))).
Definition term172 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) x0)) \/ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term207 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term254 (x0 : nat) (x1 : nat) := ~ ((Nat.pow x0 x1) = (NUMERAL 0)).
Definition term132 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term232 := forall y0 : nat, (forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) /\ (forall y1 : nat, (~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term99 (x0 : nat) := (~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0))) -> False.
Definition term54 := forall y0 : nat, (Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) -> Peano.lt (S y0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (S y0)).
Definition term283 := ~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0)).
Definition term216 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) x1).
Definition term124 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term142 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term59 := fun y0 : nat => (fun y1 : nat => Peano.lt y1 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1)) y0.
Definition term70 (x0 : nat) := Peano.lt (S x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term110 := ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> ~ (forall y0 : nat, forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term62 := ((Peano.lt (NUMERAL 0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0))) /\ (forall y0 : nat, (Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) -> Peano.lt (S y0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (S y0)))) -> forall y0 : nat, Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term45 (x0 : nat) := imp ((fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) x0).
Definition term155 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term281 (x0 : nat) := ((Nat.pow (S (NUMERAL (BIT1 0))) x0) = (NUMERAL 0)) -> (S (NUMERAL (BIT1 0))) = (NUMERAL 0).
Definition term61 := forall y0 : nat, Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term284 (x0 : nat) := ((S x0) = (NUMERAL 0)) -> False.
Definition term78 := or ((NUMERAL 0) = (NUMERAL 0)).
Definition term177 := forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term174 := forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0).
Definition term39 := (fun y0 : nat => Peano.lt y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0)) (NUMERAL 0).
Definition term250 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.pow y1 y2) = (NUMERAL 0))) \/ ((y1 = (NUMERAL 0)) /\ (~ (y2 = (NUMERAL 0))))) y0.
Definition term245 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.pow y1 y2) = (NUMERAL 0)) \/ ((~ (y1 = (NUMERAL 0))) \/ (y2 = (NUMERAL 0)))) y0.
Definition term188 := (forall y0 : nat, (y0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0)))) /\ ((forall y0 : nat, (~ (Peano.lt (NUMERAL 0) y0)) \/ (Peano.le (NUMERAL (BIT1 0)) y0)) /\ ((forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0)) /\ (forall y0 : nat, (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))))))).
Definition term146 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))).
Definition term125 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term156 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term264 (x0 : nat) := (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0)) -> ~ (Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0)).
Definition term179 := fun y0 : nat => (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term170 := fun y0 : nat => (~ (Peano.lt (NUMERAL 0) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term278 (x0 : nat) (x1 : nat) := imp (~ (~ ((Nat.pow x0 x1) = (NUMERAL 0)))).
Definition term257 := fun y0 : nat => forall y1 : nat, ((~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ (y0 = (NUMERAL 0))) /\ ((~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ (~ (y1 = (NUMERAL 0)))).
Definition term236 := fun y0 : nat => forall y1 : nat, (~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term235 := fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0))).
Definition term205 := fun y0 : nat => forall y1 : nat, (((Nat.pow y0 y1) = (NUMERAL 0)) \/ ((~ (y0 = (NUMERAL 0))) \/ (y1 = (NUMERAL 0)))) /\ ((~ ((Nat.pow y0 y1) = (NUMERAL 0))) \/ ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term123 := fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term137 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term35 := NUMERAL (BIT1 0).
Definition term204 (x0 : nat) := forall y0 : nat, (((Nat.pow x0 y0) = (NUMERAL 0)) \/ ((~ (x0 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0)))) /\ ((~ ((Nat.pow x0 y0) = (NUMERAL 0))) \/ ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))).
Definition term265 (x0 : Prop) := x0 -> ~ x0.
Definition term176 := fun y0 : nat => (~ (Peano.le (NUMERAL (BIT1 0)) y0)) \/ (Peano.lt (NUMERAL 0) y0).
Definition term275 (x0 : nat) (x1 : nat) := (~ (~ ((Nat.pow x1 x0) = (NUMERAL 0)))) -> x1 = (NUMERAL 0).
Definition term122 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term95 (x0 : nat) := Peano.lt (NUMERAL 0) (Nat.pow (S (NUMERAL (BIT1 0))) x0).
Definition term90 (x0 : nat) := Peano.lt (NUMERAL 0) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0).
