Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term224 (x0 : nat) (x1 : type1605) := (fun y0 : type1605 => (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 y1 (S y1)) -> (~ (y0 x0 (S x0))) -> False) x1.
Definition term223 (x0 : nat) := (fun y0 : nat => forall y1 : type1605, (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 y2 (S y2)) -> (~ (y1 y0 (S y0))) -> False) x0.
Definition term269 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 (S (Nat.add x1 x2)) (S (S (Nat.add x1 x2))).
Definition term273 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (x1 x0 x3) \/ (~ (x1 x2 x3)).
Definition term289 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := imp ((x1 x0 x2) /\ (x1 x2 x3)).
Definition term107 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((x3 = (Nat.add x2 (S x0))) = x4) -> (x4 -> (x1 x2 x3) = x5) -> ((x3 = (Nat.add x2 (S x0))) -> x1 x2 x3) = (x4 -> x5).
Definition term267 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (x0 x1 (S (Nat.add x1 x2)))) -> x0 x1 (S (Nat.add x1 x2)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, forall y2 : a1, y0 y1 y2) = (forall y1 : a1, forall y2 : a0, y0 y2 y1)) x0.
Definition term222 := (~ False) -> False.
Definition term297 (x0 : type1605) := (forall y0 : nat, x0 y0 (S y0)) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1.
Definition term280 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (~ ((~ (x1 x2 x0)) \/ (~ (x1 x0 x3)))) -> x1 x2 x3.
Definition term296 (x0 : nat) (x1 : nat) (x2 : type1605) := (fun y0 : type1605 => (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 y1 (S y1)) -> (y0 x0 (S (Nat.add x0 x1))) -> (~ (y0 x0 (S (S (Nat.add x0 x1))))) -> False) x2.
Definition term178 (x0 : type1605) (x1 : nat) := forall y0 : nat, (x0 x1 (S (Nat.add x1 y0))) -> x0 x1 (S (Nat.add x1 (S y0))).
Definition term176 (x0 : type1605) (x1 : nat) := fun y0 : nat => (x0 x1 (S (Nat.add x1 y0))) -> x0 x1 (S (Nat.add x1 (S y0))).
Definition term225 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False.
Definition term55 (x0 : type1605) (x1 : nat) := forall y0 : nat, (Peano.lt x1 y0) -> x0 x1 y0.
Definition term60 (x0 : nat) := Peano.lt x0 (S x0).
Definition term293 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 (S (S (Nat.add x1 x2)))) -> False.
Definition term154 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, (fun y1 : nat => y1 = (Nat.add x0 (S x1))) y0).
Definition term92 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, (fun y1 : nat => x0 = (Nat.add x1 (S y1))) y0).
Definition term270 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (x0 (S (Nat.add x1 x2)) (S (S (Nat.add x1 x2))))) -> x0 (S (Nat.add x1 x2)) (S (S (Nat.add x1 x2))).
Definition term198 (x0 : Prop) := ~ (~ x0).
Definition term294 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : type1605, (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((y2 y3 y4) /\ (y2 y4 y5)) -> y2 y3 y5) -> (forall y3 : nat, y2 y3 (S y3)) -> (y2 y1 (S (Nat.add y1 y0))) -> (~ (y2 y1 (S (S (Nat.add y1 y0))))) -> False) x0.
Definition term171 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 x1 (S (Nat.add x1 y0))) (S x2).
Definition term47 (x0 : type1605) := forall y0 : nat, x0 y0 (S y0).
Definition term240 (x0 : nat) (x1 : nat) := forall y0 : type1605, (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 y1 (S y1)) -> (y0 x0 (S (Nat.add x0 x1))) -> y0 x0 (S (S (Nat.add x0 x1))).
Definition term239 (x0 : nat) (x1 : nat) := forall y0 : type1605, (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 y1 (S y1)) -> (y0 x0 (S (Nat.add x0 x1))) -> (~ (y0 x0 (S (S (Nat.add x0 x1))))) -> False.
Definition term207 (x0 : nat) := forall y0 : type1605, (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 y1 (S y1)) -> y0 x0 (S x0).
Definition term194 (x0 : type1605) (x1 : nat) := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False.
Definition term144 (x0 : nat) (x1 : nat) := fun y0 : nat => y0 = (Nat.add x0 (S x1)).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term156 (x0 : type1605) (x1 : nat) (x2 : nat) := (exists y0 : nat, y0 = (Nat.add x1 (S x2))) -> x0 x1 (Nat.add x1 (S x2)).
Definition term268 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (x0 x1 (S (Nat.add x1 x2))).
Definition term68 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term62 (x0 : nat) := or (x0 = x0).
Definition term53 (x0 : type1605) (x1 : Prop) := ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> (forall y0 : nat, x0 y0 (S y0)) = x1) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> forall y0 : nat, x0 y0 (S y0)) = ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> x1).
Definition term250 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (~ (x1 x0 x2)) \/ (~ (x1 x2 x3)).
Definition term195 (x0 : type1605) (x1 : nat) := (((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False.
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term190 (x0 : Prop) := (~ x0) -> False.
Definition term205 (x0 : nat) := fun y0 : type1605 => (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 y1 (S y1)) -> y0 x0 (S x0).
Definition term8 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term288 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := imp (~ ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3)))).
Definition term237 (x0 : nat) (x1 : nat) := fun y0 : type1605 => (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 y1 (S y1)) -> (y0 x0 (S (Nat.add x0 x1))) -> (~ (y0 x0 (S (S (Nat.add x0 x1))))) -> False.
Definition term226 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (x0 x1 (S (S (Nat.add x1 x2)))).
Definition term56 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt x1 y0) -> x0 x1 y0) x2.
Definition term58 (x0 : type1605) (x1 : nat) (x2 : nat) := (Peano.lt x1 x2) -> (x0 x1 x2) = True.
Definition term189 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 x1 (S (S (Nat.add x1 x2))).
Definition term184 (x0 : type1605) (x1 : nat) := forall y0 : nat, (fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) y0.
Definition term214 (x0 : nat) (x1 : type1605) (x2 : nat) := forall y0 : nat, ((x1 x2 x0) /\ (x1 x0 y0)) -> x1 x2 y0.
Definition term95 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((exists y0 : nat, x2 = (Nat.add x1 (S y0))) -> x0 x1 x2).
Definition term94 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x2 = (Nat.add x1 (S y1))) y0) -> x0 x1 x2).
Definition term52 (x0 : type1605) (x1 : Prop) := ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1)) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> (forall y0 : nat, x0 y0 (S y0)) = x1) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> forall y0 : nat, x0 y0 (S y0)) = ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> x1).
Definition term201 (x0 : type1605) (x1 : nat) := (forall y0 : nat, x0 y0 (S y0)) -> x0 x1 (S x1).
Definition term179 (x0 : type1605) (x1 : nat) := ((fun y0 : nat => x0 x1 (S (Nat.add x1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) y0) -> (fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) (S y0)).
Definition term159 (x0 : type1605) (x1 : nat) (x2 : nat) := True -> x0 x1 (S (Nat.add x1 x2)).
Definition term32 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1))).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => y0 = (Nat.add x0 (S x1))) x2.
Definition term279 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term233 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 (S (Nat.add x1 x2))) -> x0 x1 (S (S (Nat.add x1 x2))).
Definition term70 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> (forall y0 : nat, x0 y0 (S y0)) = True.
Definition term142 (x0 : type1605) (x1 : nat) (x2 : nat) := forall y0 : nat, ((fun y1 : nat => y1 = (Nat.add x1 (S x2))) y0) -> x0 x1 (Nat.add x1 (S x2)).
Definition term299 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) = (forall y0 : nat, x0 y0 (S y0)).
Definition term16 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term143 (x0 : type1605) (x1 : nat) (x2 : nat) := (exists y0 : nat, (fun y1 : nat => y1 = (Nat.add x1 (S x2))) y0) -> x0 x1 (Nat.add x1 (S x2)).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, forall y1 : a1, x0 y0 y1.
Definition term101 (x0 : type1605) (x1 : nat) (x2 : nat) := fun y0 : nat => (x2 = (Nat.add x1 (S y0))) -> x0 x1 x2.
Definition term73 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> True.
Definition term220 (x0 : Prop) := (~ x0) -> x0.
Definition term163 (x0 : type1605) (x1 : nat) := (((fun y0 : nat => x0 x1 (S (Nat.add x1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) y0) -> (fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) y0.
Definition term72 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> forall y0 : nat, x0 y0 (S y0).
Definition term295 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : type1605, (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 y2 (S y2)) -> (y1 y0 (S (Nat.add y0 x0))) -> (~ (y1 y0 (S (S (Nat.add y0 x0))))) -> False) x1.
Definition term242 (x0 : nat) := fun y0 : nat => forall y1 : type1605, (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 y2 (S y2)) -> (y1 y0 (S (Nat.add y0 x0))) -> y1 y0 (S (S (Nat.add y0 x0))).
Definition term241 (x0 : nat) := fun y0 : nat => forall y1 : type1605, (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 y2 (S y2)) -> (y1 y0 (S (Nat.add y0 x0))) -> (~ (y1 y0 (S (S (Nat.add y0 x0))))) -> False.
Definition term209 := fun y0 : nat => forall y1 : type1605, (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 y2 (S y2)) -> y1 y0 (S y0).
Definition term208 := fun y0 : nat => forall y1 : type1605, (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 y2 (S y2)) -> (~ (y1 y0 (S y0))) -> False.
Definition term18 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y1 = y0) x0.
Definition term282 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term204 (x0 : nat) := fun y0 : type1605 => (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 y1 (S y1)) -> (~ (y0 x0 (S x0))) -> False.
Definition term162 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term193 (x0 : type1605) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False.
Definition term285 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (~ (x0 x1 x2)).
Definition term155 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, y0 = (Nat.add x0 (S x1))).
Definition term93 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, x0 = (Nat.add x1 (S y0))).
Definition term150 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop (forall y0 : nat, (y0 = (Nat.add x1 (S x2))) -> x0 x1 (Nat.add x1 (S x2))).
Definition term149 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => y1 = (Nat.add x1 (S x2))) y0) -> x0 x1 (Nat.add x1 (S x2))).
Definition term181 (x0 : type1605) (x1 : nat) := imp (((fun y0 : nat => x0 x1 (S (Nat.add x1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) y0) -> (fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) (S y0))).
Definition term275 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (~ (x1 x0 x2)) \/ ((x1 x0 x3) \/ (~ (x1 x2 x3))).
Definition term75 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Peano.lt x1 x2) = y0) -> (y0 -> (x0 x1 x2) = y1) -> ((Peano.lt x1 x2) -> x0 x1 x2) = (y0 -> y1)) x3.
Definition term254 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := ((~ (x1 x2 x0)) \/ (~ (x1 x0 x3))) \/ (x1 x2 x3).
Definition term251 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := or (~ ((x1 x0 x2) /\ (x1 x2 x3))).
Definition term61 (x0 : nat) := (x0 = x0) \/ (Peano.lt x0 x0).
Definition term17 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term264 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((~ (x1 x2 x0)) \/ (~ (x1 x0 y0))) \/ (x1 x2 y0)) x3.
Definition term232 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False.
Definition term235 (x0 : type1605) (x1 : nat) (x2 : nat) := (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> x0 x1 (S (S (Nat.add x1 x2))).
Definition term64 (x0 : type1605) (x1 : nat) := x0 x1 (S x1).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term54 (x0 : type1605) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) x1.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => (forall y1 : a0, (x0 y1) -> y0) = ((exists y1 : a0, x0 y1) -> y0)) x1.
Definition term110 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 x1 (Nat.add x1 (S x2)).
Definition term177 (x0 : type1605) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) y0) -> (fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) (S y0).
Definition term265 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (~ (x1 x2 x0)) \/ ((~ (x1 x0 x3)) \/ (x1 x2 x3)).
Definition term258 (x0 : type1605) (x1 : nat) := fun y0 : nat => forall y1 : nat, ((~ (x0 x1 y0)) \/ (~ (x0 y0 y1))) \/ (x0 x1 y1).
Definition term215 (x0 : type1605) (x1 : nat) := fun y0 : nat => forall y1 : nat, ((x0 x1 y0) /\ (x0 y0 y1)) -> x0 x1 y1.
Definition term119 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1.
Definition term41 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term113 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (x0 = (Nat.add x2 (S x3))) -> x1 x2 (Nat.add x2 (S x3)).
Definition term50 (x0 : type1605) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 y1 y2) = x1) -> (x1 -> (forall y1 : nat, x0 y1 (S y1)) = y0) -> ((forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 y1 y2) -> forall y1 : nat, x0 y1 (S y1)) = (x1 -> y0)) x2.
Definition term212 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := ((x1 x2 x0) /\ (x1 x0 x3)) -> x1 x2 x3.
Definition term59 (x0 : type1605) (x1 : nat) := (Peano.lt x1 (S x1)) -> (x0 x1 (S x1)) = True.
Definition term15 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term42 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term102 (x0 : type1605) (x1 : nat) (x2 : nat) := forall y0 : nat, (x2 = (Nat.add x1 (S y0))) -> x0 x1 x2.
Definition term166 (x0 : type1605) (x1 : nat) := and ((fun y0 : nat => x0 x1 (S (Nat.add x1 y0))) (NUMERAL 0)).
Definition term153 (x0 : nat) (x1 : nat) := exists y0 : nat, y0 = (Nat.add x0 (S x1)).
Definition term234 (x0 : type1605) (x1 : nat) (x2 : nat) := (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False.
Definition term78 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((Peano.lt x1 x2) = x3) -> (x3 -> (x0 x1 x2) = x4) -> ((Peano.lt x1 x2) -> x0 x1 x2) = (x3 -> x4).
Definition term168 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 x1 (S (Nat.add x1 y0))) x2.
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := imp (x0 = (Nat.add x1 (S x2))).
Definition term139 (x0 : type1605) (x1 : nat) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (Nat.add x1 (S y3))) -> x0 x1 (Nat.add x1 (S y3))) y1 y0.
Definition term206 (x0 : nat) := forall y0 : type1605, (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 y1 (S y1)) -> (~ (y0 x0 (S x0))) -> False.
Definition term98 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := ((fun y0 : nat => x3 = (Nat.add x2 (S y0))) x0) -> x1 x2 x3.
Definition term100 (x0 : type1605) (x1 : nat) (x2 : nat) := fun y0 : nat => ((fun y1 : nat => x2 = (Nat.add x1 (S y1))) y0) -> x0 x1 x2.
Definition term134 (x0 : type1605) (x1 : nat) := @eq Prop (forall y0 : nat, forall y1 : nat, (y0 = (Nat.add x1 (S y1))) -> x0 x1 (Nat.add x1 (S y1))).
Definition term133 (x0 : type1605) (x1 : nat) := @eq Prop (forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (Nat.add x1 (S y3))) -> x0 x1 (Nat.add x1 (S y3))) y0 y1).
Definition term199 (x0 : type1605) := imp (forall y0 : nat, x0 y0 (S y0)).
Definition term86 (x0 : type1605) (x1 : nat) (x2 : nat) := (exists y0 : nat, (fun y1 : nat => x2 = (Nat.add x1 (S y1))) y0) -> x0 x1 x2.
Definition term83 (x0 : type1605) (x1 : nat) (x2 : nat) := (exists y0 : nat, x2 = (Nat.add x1 (S y0))) -> x0 x1 x2.
Definition term135 (x0 : type1605) (x1 : nat) (x2 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (y1 = (Nat.add x1 (S y2))) -> x0 x1 (Nat.add x1 (S y2))) y0 x2.
Definition term175 (x0 : type1605) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) y0) -> (fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) (S y0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0)) x1.
Definition term203 (x0 : type1605) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> x0 x1 (S x1).
Definition term14 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term221 (x0 : type1605) (x1 : nat) := (x0 x1 (S x1)) -> False.
Definition term287 (x0 : type1605) (x1 : nat) (x2 : nat) := and (x0 x1 x2).
Definition term253 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (~ ((x1 x2 x0) /\ (x1 x0 x3))) \/ (x1 x2 x3).
Definition term81 (x0 : type1605) (x1 : nat) (x2 : nat) := (exists y0 : nat, x2 = (Nat.add x1 (S y0))) -> (x0 x1 x2) = (x0 x1 x2).
Definition term281 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term261 (x0 : type1605) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (x0 y0 y1)) \/ (~ (x0 y1 y2))) \/ (x0 y0 y2).
Definition term259 (x0 : type1605) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((~ (x0 x1 y0)) \/ (~ (x0 y0 y1))) \/ (x0 x1 y1).
Definition term248 := forall y0 : nat, forall y1 : nat, forall y2 : type1605, (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((y2 y3 y4) /\ (y2 y4 y5)) -> y2 y3 y5) -> (forall y3 : nat, y2 y3 (S y3)) -> (y2 y1 (S (Nat.add y1 y0))) -> y2 y1 (S (S (Nat.add y1 y0))).
Definition term247 := forall y0 : nat, forall y1 : nat, forall y2 : type1605, (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((y2 y3 y4) /\ (y2 y4 y5)) -> y2 y3 y5) -> (forall y3 : nat, y2 y3 (S y3)) -> (y2 y1 (S (Nat.add y1 y0))) -> (~ (y2 y1 (S (S (Nat.add y1 y0))))) -> False.
Definition term244 (x0 : nat) := forall y0 : nat, forall y1 : type1605, (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 y2 (S y2)) -> (y1 y0 (S (Nat.add y0 x0))) -> y1 y0 (S (S (Nat.add y0 x0))).
Definition term243 (x0 : nat) := forall y0 : nat, forall y1 : type1605, (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 y2 (S y2)) -> (y1 y0 (S (Nat.add y0 x0))) -> (~ (y1 y0 (S (S (Nat.add y0 x0))))) -> False.
Definition term216 (x0 : type1605) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 x1 y0) /\ (x0 y0 y1)) -> x0 x1 y1.
Definition term211 := forall y0 : nat, forall y1 : type1605, (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 y2 (S y2)) -> y1 y0 (S y0).
Definition term210 := forall y0 : nat, forall y1 : type1605, (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 y2 (S y2)) -> (~ (y1 y0 (S y0))) -> False.
Definition term141 (x0 : type1605) (x1 : nat) := forall y0 : nat, forall y1 : nat, (y1 = (Nat.add x1 (S y0))) -> x0 x1 (Nat.add x1 (S y0)).
Definition term125 (x0 : type1605) (x1 : nat) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (Nat.add x1 (S y3))) -> x0 x1 (Nat.add x1 (S y3))) y1 y0.
Definition term124 (x0 : type1605) (x1 : nat) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (Nat.add x1 (S y3))) -> x0 x1 (Nat.add x1 (S y3))) y0 y1.
Definition term123 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y1 y0.
Definition term122 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term121 (x0 : type1605) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (y1 = (Nat.add y0 (S y2))) -> x0 y0 (Nat.add y0 (S y2)).
Definition term118 (x0 : type1605) (x1 : nat) := forall y0 : nat, forall y1 : nat, (y0 = (Nat.add x1 (S y1))) -> x0 x1 (Nat.add x1 (S y1)).
Definition term46 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1.
Definition term36 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term35 (x0 : type1605) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2.
Definition term9 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term276 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (x1 x0 x3) \/ ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3))).
Definition term57 (x0 : type1605) (x1 : nat) (x2 : nat) := (Peano.lt x1 x2) -> x0 x1 x2.
Definition term79 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : Prop) := ((Peano.lt x2 x1) = (exists y0 : nat, x1 = (Nat.add x2 (S y0)))) -> ((exists y0 : nat, x1 = (Nat.add x2 (S y0))) -> (x0 x2 x1) = x3) -> ((Peano.lt x2 x1) -> x0 x2 x1) = ((exists y0 : nat, x1 = (Nat.add x2 (S y0))) -> x3).
Definition term263 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (x0 x1 y0)) \/ (~ (x0 y0 y1))) \/ (x0 x1 y1)) x2.
Definition term262 (x0 : type1605) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (x0 y0 y1)) \/ (~ (x0 y1 y2))) \/ (x0 y0 y2)) x1.
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a1, forall y1 : a0, x0 y1 y0.
Definition term82 (x0 : type1605) (x1 : nat) (x2 : nat) := ((exists y0 : nat, x2 = (Nat.add x1 (S y0))) -> (x0 x1 x2) = (x0 x1 x2)) -> ((Peano.lt x1 x2) -> x0 x1 x2) = ((exists y0 : nat, x2 = (Nat.add x1 (S y0))) -> x0 x1 x2).
Definition term256 (x0 : nat) (x1 : type1605) (x2 : nat) := fun y0 : nat => ((~ (x1 x2 x0)) \/ (~ (x1 x0 y0))) \/ (x1 x2 y0).
Definition term108 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x1 = (Nat.add x2 (S x3))) = (x1 = (Nat.add x2 (S x3)))) -> ((x1 = (Nat.add x2 (S x3))) -> (x0 x2 x1) = x4) -> ((x1 = (Nat.add x2 (S x3))) -> x0 x2 x1) = ((x1 = (Nat.add x2 (S x3))) -> x4).
Definition term40 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term67 := forall y0 : nat, True.
Definition term174 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 (S (Nat.add x1 x2))) -> x0 x1 (S (Nat.add x1 (S x2))).
Definition term136 (x0 : type1605) (x1 : nat) (x2 : nat) := fun y0 : nat => (y0 = (Nat.add x1 (S x2))) -> x0 x1 (Nat.add x1 (S x2)).
Definition term147 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := ((fun y0 : nat => y0 = (Nat.add x2 (S x3))) x0) -> x1 x2 (Nat.add x2 (S x3)).
Definition term292 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> x0 x1 (S (S (Nat.add x1 x2))).
Definition term227 (x0 : type1605) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term84 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) -> x1.
Definition term255 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (x1 x0 x2) /\ (x1 x2 x3).
Definition term87 (x0 : type1605) (x1 : nat) (x2 : nat) := forall y0 : nat, ((fun y1 : nat => x2 = (Nat.add x1 (S y1))) y0) -> x0 x1 x2.
Definition term257 (x0 : nat) (x1 : type1605) (x2 : nat) := forall y0 : nat, ((~ (x1 x2 x0)) \/ (~ (x1 x0 y0))) \/ (x1 x2 y0).
Definition term126 (x0 : type1605) (x1 : nat) := fun y0 : nat => fun y1 : nat => (y0 = (Nat.add x1 (S y1))) -> x0 x1 (Nat.add x1 (S y1)).
Definition term185 (x0 : type1605) (x1 : nat) := ((x0 x1 (S (Nat.add x1 (NUMERAL 0)))) /\ (forall y0 : nat, (x0 x1 (S (Nat.add x1 y0))) -> x0 x1 (S (Nat.add x1 (S y0))))) -> forall y0 : nat, x0 x1 (S (Nat.add x1 y0)).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((exists y2 : a0, y0 y2) -> y1) = (forall y2 : a0, (y0 y2) -> y1)) x0.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, (forall y2 : a0, (y0 y2) -> y1) = ((exists y2 : a0, y0 y2) -> y1)) x0.
Definition term200 (x0 : type1605) (x1 : nat) := (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False.
Definition term65 (x0 : type1605) := fun y0 : nat => x0 y0 (S y0).
Definition term66 := fun y0 : nat => True.
Definition term38 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term271 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (x0 (S (Nat.add x1 x2)) (S (S (Nat.add x1 x2)))).
Definition term252 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := or ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3))).
Definition term85 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) -> x1.
Definition term111 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (x0 = (Nat.add x2 (S x3))) -> (x1 x2 x0) = (x1 x2 (Nat.add x2 (S x3))).
Definition term238 (x0 : nat) (x1 : nat) := fun y0 : type1605 => (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 y1 (S y1)) -> (y0 x0 (S (Nat.add x0 x1))) -> y0 x0 (S (S (Nat.add x0 x1))).
Definition term157 (x0 : nat) := exists y0 : nat, y0 = x0.
Definition term105 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) (x4 : Prop) := forall y0 : Prop, ((x3 = (Nat.add x2 (S x0))) = x4) -> (x4 -> (x1 x2 x3) = y0) -> ((x3 = (Nat.add x2 (S x0))) -> x1 x2 x3) = (x4 -> y0).
Definition term76 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, ((Peano.lt x1 x2) = x3) -> (x3 -> (x0 x1 x2) = y0) -> ((Peano.lt x1 x2) -> x0 x1 x2) = (x3 -> y0).
Definition term49 (x0 : type1605) (x1 : Prop) := forall y0 : Prop, ((forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 y1 y2) = x1) -> (x1 -> (forall y1 : nat, x0 y1 (S y1)) = y0) -> ((forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 y1 y2) -> forall y1 : nat, x0 y1 (S y1)) = (x1 -> y0).
Definition term43 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term19 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term290 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 (S (Nat.add x1 x2))) /\ (x0 (S (Nat.add x1 x2)) (S (S (Nat.add x1 x2)))).
Definition term34 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 (S y0)).
Definition term131 (x0 : type1605) (x1 : nat) (x2 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (y1 = (Nat.add x1 (S y2))) -> x0 x1 (Nat.add x1 (S y2))) x2 y0.
Definition term152 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => y1 = (Nat.add x0 (S x1))) y0.
Definition term91 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.add x1 (S y1))) y0.
Definition term218 (x0 : type1605) (x1 : nat) := (fun y0 : nat => x0 y0 (S y0)) x1.
Definition term266 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (x0 x1 x2).
Definition term132 (x0 : type1605) (x1 : nat) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (y2 = (Nat.add x1 (S y3))) -> x0 x1 (Nat.add x1 (S y3))) y0 y1.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term103 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, ((x3 = (Nat.add x2 (S x0))) = y0) -> (y0 -> (x1 x2 x3) = y1) -> ((x3 = (Nat.add x2 (S x0))) -> x1 x2 x3) = (y0 -> y1).
Definition term74 (x0 : type1605) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, ((Peano.lt x1 x2) = y0) -> (y0 -> (x0 x1 x2) = y1) -> ((Peano.lt x1 x2) -> x0 x1 x2) = (y0 -> y1).
Definition term45 (x0 : type1605) := forall y0 : Prop, forall y1 : Prop, ((forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 y2 y3) = y0) -> (y0 -> (forall y2 : nat, x0 y2 (S y2)) = y1) -> ((forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 y2 y3) -> forall y2 : nat, x0 y2 (S y2)) = (y0 -> y1).
Definition term44 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term272 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (~ (x1 x0 x3)) \/ (x1 x2 x3).
Definition term7 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term230 (x0 : type1605) (x1 : nat) (x2 : nat) := (((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False.
Definition term39 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term213 (x0 : nat) (x1 : type1605) (x2 : nat) := fun y0 : nat => ((x1 x2 x0) /\ (x1 x0 y0)) -> x1 x2 y0.
Definition term130 (x0 : type1605) (x1 : nat) (x2 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (y1 = (Nat.add x1 (S y2))) -> x0 x1 (Nat.add x1 (S y2))) x2 y0.
Definition term300 := forall y0 : type1605, (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> y0 y1 y2) = (forall y1 : nat, y0 y1 (S y1)).
Definition term99 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (x3 = (Nat.add x2 (S x0))) -> x1 x2 x3.
Definition term196 (x0 : type1605) (x1 : nat) := (((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (~ (x0 x1 (S x1))) -> False.
Definition term138 (x0 : type1605) (x1 : nat) (x2 : nat) := forall y0 : nat, (y0 = (Nat.add x1 (S x2))) -> x0 x1 (Nat.add x1 (S x2)).
Definition term115 (x0 : nat) (x1 : type1605) (x2 : nat) := forall y0 : nat, (x0 = (Nat.add x2 (S y0))) -> x1 x2 (Nat.add x2 (S y0)).
Definition term128 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => fun y1 : nat => (y0 = (Nat.add x1 (S y1))) -> x0 x1 (Nat.add x1 (S y1))) x2 x3.
Definition term77 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((Peano.lt x1 x2) = x3) -> (x3 -> (x0 x1 x2) = y0) -> ((Peano.lt x1 x2) -> x0 x1 x2) = (x3 -> y0)) x4.
Definition term51 (x0 : type1605) (x1 : Prop) (x2 : Prop) := ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) = x1) -> (x1 -> (forall y0 : nat, x0 y0 (S y0)) = x2) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> forall y0 : nat, x0 y0 (S y0)) = (x1 -> x2).
Definition term112 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := ((x0 = (Nat.add x2 (S x3))) -> (x1 x2 x0) = (x1 x2 (Nat.add x2 (S x3)))) -> ((x0 = (Nat.add x2 (S x3))) -> x1 x2 x0) = ((x0 = (Nat.add x2 (S x3))) -> x1 x2 (Nat.add x2 (S x3))).
Definition term278 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := @eq Prop ((x1 x0 x3) \/ ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3)))).
Definition term71 (x0 : type1605) := ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> (forall y0 : nat, x0 y0 (S y0)) = True) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> forall y0 : nat, x0 y0 (S y0)) = ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> True).
Definition term106 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((x3 = (Nat.add x2 (S x0))) = x4) -> (x4 -> (x1 x2 x3) = y0) -> ((x3 = (Nat.add x2 (S x0))) -> x1 x2 x3) = (x4 -> y0)) x5.
Definition term170 (x0 : type1605) (x1 : nat) (x2 : nat) := imp (x0 x1 (S (Nat.add x1 x2))).
Definition term167 (x0 : type1605) (x1 : nat) := and (x0 x1 (S (Nat.add x1 (NUMERAL 0)))).
Definition term291 (x0 : type1605) (x1 : nat) (x2 : nat) := ((x0 x1 (S (Nat.add x1 x2))) /\ (x0 (S (Nat.add x1 x2)) (S (S (Nat.add x1 x2))))) -> x0 x1 (S (S (Nat.add x1 x2))).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0).
Definition term187 (x0 : nat) (x1 : nat) := S (Nat.add x0 (S x1)).
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term31 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 (S y2)))) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term231 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (~ (x0 x1 (S (S (Nat.add x1 x2))))).
Definition term182 (x0 : type1605) (x1 : nat) := imp ((x0 x1 (S (Nat.add x1 (NUMERAL 0)))) /\ (forall y0 : nat, (x0 x1 (S (Nat.add x1 y0))) -> x0 x1 (S (Nat.add x1 (S y0))))).
Definition term137 (x0 : type1605) (x1 : nat) (x2 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (y1 = (Nat.add x1 (S y2))) -> x0 x1 (Nat.add x1 (S y2))) y0 x2.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 = (Nat.add x1 (S y0))) x2.
Definition term191 (x0 : type1605) (x1 : nat) := (~ (x0 x1 (S x1))) -> False.
Definition term114 (x0 : nat) (x1 : type1605) (x2 : nat) := fun y0 : nat => (x0 = (Nat.add x2 (S y0))) -> x1 x2 (Nat.add x2 (S y0)).
Definition term148 (x0 : type1605) (x1 : nat) (x2 : nat) := fun y0 : nat => ((fun y1 : nat => y1 = (Nat.add x1 (S x2))) y0) -> x0 x1 (Nat.add x1 (S x2)).
Definition term186 (x0 : nat) := S (Nat.add x0 (NUMERAL 0)).
Definition term80 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : Prop) := ((exists y0 : nat, x1 = (Nat.add x2 (S y0))) -> (x0 x2 x1) = x3) -> ((Peano.lt x2 x1) -> x0 x2 x1) = ((exists y0 : nat, x1 = (Nat.add x2 (S y0))) -> x3).
Definition term161 (x0 : type1605) (x1 : nat) := forall y0 : nat, x0 x1 (S (Nat.add x1 y0)).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, (forall y1 : a0, (x0 y1) -> y0) = ((exists y1 : a0, x0 y1) -> y0).
Definition term88 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 (S y0)).
Definition term219 (x0 : type1605) (x1 : nat) := (~ (x0 x1 (S x1))) -> x0 x1 (S x1).
Definition term283 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := ~ ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3))).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term13 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term48 (x0 : type1605) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 y2 y3) = y0) -> (y0 -> (forall y2 : nat, x0 y2 (S y2)) = y1) -> ((forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 y2 y3) -> forall y2 : nat, x0 y2 (S y2)) = (y0 -> y1)) x1.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term164 (x0 : type1605) (x1 : nat) := (fun y0 : nat => x0 x1 (S (Nat.add x1 y0))) (NUMERAL 0).
Definition term151 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => y1 = (Nat.add x0 (S x1))) y0.
Definition term90 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.add x1 (S y1))) y0.
Definition term69 (x0 : Prop) := forall y0 : nat, x0.
Definition term183 (x0 : type1605) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 x1 (S (Nat.add x1 y1))) y0.
Definition term229 (x0 : type1605) (x1 : nat) (x2 : nat) := (((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False.
Definition term129 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (fun y0 : nat => (x0 = (Nat.add x2 (S y0))) -> x1 x2 (Nat.add x2 (S y0))) x3.
Definition term127 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (y0 = (Nat.add x1 (S y1))) -> x0 x1 (Nat.add x1 (S y1))) x2.
Definition term173 (x0 : type1605) (x1 : nat) (x2 : nat) := ((fun y0 : nat => x0 x1 (S (Nat.add x1 y0))) x2) -> (fun y0 : nat => x0 x1 (S (Nat.add x1 y0))) (S x2).
Definition term116 (x0 : type1605) (x1 : nat) := fun y0 : nat => (Peano.lt x1 y0) -> x0 x1 y0.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term180 (x0 : type1605) (x1 : nat) := (x0 x1 (S (Nat.add x1 (NUMERAL 0)))) /\ (forall y0 : nat, (x0 x1 (S (Nat.add x1 y0))) -> x0 x1 (S (Nat.add x1 (S y0)))).
Definition term169 (x0 : type1605) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => x0 x1 (S (Nat.add x1 y0))) x2).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => y0 = (Nat.add x0 (S x1))) x2).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => x0 = (Nat.add x1 (S y0))) x2).
Definition term165 (x0 : type1605) (x1 : nat) := x0 x1 (S (Nat.add x1 (NUMERAL 0))).
Definition term274 (x0 : type1605) (x1 : nat) (x2 : nat) := or (~ (x0 x1 x2)).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1)))) x1.
Definition term298 (x0 : type1605) := ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1) -> forall y0 : nat, x0 y0 (S y0)) /\ ((forall y0 : nat, x0 y0 (S y0)) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1).
Definition term104 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x3 = (Nat.add x2 (S x0))) = y0) -> (y0 -> (x1 x2 x3) = y1) -> ((x3 = (Nat.add x2 (S x0))) -> x1 x2 x3) = (y0 -> y1)) x4.
Definition term63 (x0 : nat) := True \/ (Peano.lt x0 x0).
Definition term109 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x1 = (Nat.add x2 (S x3))) -> (x0 x2 x1) = x4) -> ((x1 = (Nat.add x2 (S x3))) -> x0 x2 x1) = ((x1 = (Nat.add x2 (S x3))) -> x4).
Definition term277 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x1 x2 x0)) \/ ((~ (x1 x0 x3)) \/ (x1 x2 x3))).
Definition term202 (x0 : type1605) := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2).
Definition term158 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 x1 (S (Nat.add x1 x2)).
Definition term192 (x0 : type1605) (x1 : nat) := ~ (x0 x1 (S x1)).
Definition term172 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 x1 (S (Nat.add x1 (S x2))).
Definition term284 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (~ (~ (x1 x0 x2))) /\ (~ (~ (x1 x2 x3))).
Definition term249 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := ~ ((x1 x0 x2) /\ (x1 x2 x3)).
Definition term160 (x0 : type1605) (x1 : nat) := fun y0 : nat => x0 x1 (S (Nat.add x1 y0)).
Definition term286 (x0 : type1605) (x1 : nat) (x2 : nat) := and (~ (~ (x0 x1 x2))).
Definition term140 (x0 : type1605) (x1 : nat) := fun y0 : nat => forall y1 : nat, (y1 = (Nat.add x1 (S y0))) -> x0 x1 (Nat.add x1 (S y0)).
Definition term117 (x0 : type1605) (x1 : nat) := fun y0 : nat => forall y1 : nat, (y0 = (Nat.add x1 (S y1))) -> x0 x1 (Nat.add x1 (S y1)).
Definition term236 (x0 : type1605) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> x0 x1 (S (S (Nat.add x1 x2))).
Definition term260 (x0 : type1605) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (x0 y0 y1)) \/ (~ (x0 y1 y2))) \/ (x0 y0 y2).
Definition term246 := fun y0 : nat => forall y1 : nat, forall y2 : type1605, (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((y2 y3 y4) /\ (y2 y4 y5)) -> y2 y3 y5) -> (forall y3 : nat, y2 y3 (S y3)) -> (y2 y1 (S (Nat.add y1 y0))) -> y2 y1 (S (S (Nat.add y1 y0))).
Definition term245 := fun y0 : nat => forall y1 : nat, forall y2 : type1605, (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((y2 y3 y4) /\ (y2 y4 y5)) -> y2 y3 y5) -> (forall y3 : nat, y2 y3 (S y3)) -> (y2 y1 (S (Nat.add y1 y0))) -> (~ (y2 y1 (S (S (Nat.add y1 y0))))) -> False.
Definition term217 (x0 : type1605) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2.
Definition term120 (x0 : type1605) := fun y0 : nat => forall y1 : nat, forall y2 : nat, (y1 = (Nat.add y0 (S y2))) -> x0 y0 (Nat.add y0 (S y2)).
Definition term228 (x0 : type1605) (x1 : nat) (x2 : nat) := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 y0 (S y0)) -> (x0 x1 (S (Nat.add x1 x2))) -> (~ (x0 x1 (S (S (Nat.add x1 x2))))) -> False.
Definition term197 (x0 : type1605) (x1 : nat) := ~ (~ (x0 x1 (S x1))).
Definition term188 (x0 : nat) (x1 : nat) := S (S (Nat.add x0 x1)).
Definition term11 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
