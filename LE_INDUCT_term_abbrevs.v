Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term180 (x0 : nat) (x1 : type1605) := fun y0 : nat => (fun y1 : nat => ((Peano.le x0 y1) /\ (~ (x1 x0 y1))) /\ (forall y2 : nat, forall y3 : nat, x1 y2 (Nat.add y2 y3))) y0.
Definition term507 (x0 : type1605) (x1 : nat) (x2 : nat) := (Peano.le x1 x2) -> (fun y0 : nat => fun y1 : nat => (x0 y0 y1) -> x0 y0 (S y1)) x1 x2.
Definition term326 (x0 : type1606) := fun y0 : nat => (fun y1 : nat => fun y2 : nat -> nat => forall y3 : nat, (~ (Peano.le y1 y3)) \/ (y3 = (Nat.add y1 (y2 y3)))) y0 (x0 y0).
Definition term422 (x0 : type1606) (x1 : nat) (x2 : nat) := ~ (x2 = (Nat.add x1 (x0 x1 x2))).
Definition term425 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term474 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := imp (~ ((~ (x3 = x0)) \/ ((~ (x4 = x1)) \/ (~ (x2 x3 x4))))).
Definition term463 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop ((x0 x2 x4) \/ ((~ (x0 x1 x3)) \/ ((~ (x1 = x2)) \/ (~ (x3 = x4))))).
Definition term447 (x0 : type1606) (x1 : nat) (x2 : nat) := (~ ((Nat.add x1 (x0 x1 x2)) = x2)) -> (Nat.add x1 (x0 x1 x2)) = x2.
Definition term408 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (~ (x4 = x1)) \/ ((x2 x0 x1) \/ (~ (x2 x3 x4))).
Definition term216 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) /\ ((~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))).
Definition term4 (x0 : type1605) := ~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1))).
Definition term253 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0).
Definition term36 (x0 : nat -> Prop) := ~ (all x0).
Definition term402 := (~ False) -> False.
Definition term491 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 x1 (S x2).
Definition term484 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term517 (x0 : type1605) (x1 : nat) := fun y0 : nat => (x0 x1 (Nat.add x1 y0)) -> x0 x1 (S (Nat.add x1 y0)).
Definition term63 (x0 : type1605) (x1 : nat) := exists y0 : nat, ~ (x0 x1 (Nat.add x1 y0)).
Definition term350 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term141 (x0 : type1605) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => (Peano.le x1 y0) /\ (~ (x0 x1 y0))) x2).
Definition term432 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term279 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.le x1 x0)) \/ (x0 = (Nat.add x1 y0)).
Definition term175 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ (~ (x0 x1 (Nat.add x1 y0)))) x2.
Definition term519 (x0 : type1605) (x1 : nat) := forall y0 : nat, (x0 x1 (Nat.add x1 y0)) -> x0 x1 (S (Nat.add x1 y0)).
Definition term78 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (exists y0 : nat, exists y1 : nat, ~ (x0 y0 (Nat.add y0 y1))).
Definition term30 (x0 : type1605) (x1 : nat) := forall y0 : nat, (Peano.le x1 y0) -> x0 x1 y0.
Definition term245 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0).
Definition term223 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0).
Definition term481 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 x2) -> False.
Definition term450 (x0 : type1605) (x1 : type1606) (x2 : nat) (x3 : nat) := (~ (x0 x2 (Nat.add x2 (x1 x2 x3)))) -> x0 x2 (Nat.add x2 (x1 x2 x3)).
Definition term358 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ~ (x0 = (Nat.add x1 y1))) y0.
Definition term495 (x0 : type1605) (x1 : nat) := forall y0 : nat, (Peano.le x1 y0) -> (x0 x1 y0) -> x0 x1 (S y0).
Definition term192 (x0 : nat) (x1 : type1605) := @eq Prop ((fun y0 : Prop => y0 = (exists y1 : nat, ((forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x1 y2 y3)) /\ (~ (x1 x0 (Nat.add x0 y1)))) \/ (((Peano.le x0 y1) /\ (~ (x1 x0 y1))) /\ (forall y2 : nat, forall y3 : nat, x1 y2 (Nat.add y2 y3))))) ((exists y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x1 y1 y2)) /\ (~ (x1 x0 (Nat.add x0 y0)))) \/ (exists y0 : nat, ((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2))))).
Definition term364 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x1 x0) \/ (~ (x0 = (Nat.add x1 y0))).
Definition term383 (x0 : Prop) := ~ (~ x0).
Definition term25 (x0 : type1605) (x1 : nat) := fun y0 : nat => x0 x1 (Nat.add x1 y0).
Definition term370 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) \/ (~ (y1 = (Nat.add y0 y2)))) x0.
Definition term12 (x0 : type1605) := imp (~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))).
Definition term384 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (~ (x0 = (Nat.add x1 x2))).
Definition term72 (x0 : type1605) := and (exists y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (~ (x0 y0 y1))).
Definition term457 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) (x4 : nat) := (~ (x2 = x0)) \/ ((x1 x0 x4) \/ ((~ (x1 x2 x3)) \/ (~ (x3 = x4)))).
Definition term343 (x0 : type1606) := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ ((fun y0 : type1606 => forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2)))) x0).
Definition term186 (x0 : nat) (x1 : type1605) (x2 : nat) := ((fun y0 : nat => (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x1 y1 y2)) /\ (~ (x1 x0 (Nat.add x0 y0)))) x2) \/ ((fun y0 : nat => ((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2))) x2).
Definition term298 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1))) x2 (x1 x2).
Definition term316 (x0 : nat) (x1 : nat -> nat) := (fun y0 : nat => fun y1 : nat -> nat => forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2)))) x0 x1.
Definition term312 := forall y0 : nat, exists y1 : nat -> nat, (fun y2 : nat => fun y3 : nat -> nat => forall y4 : nat, (~ (Peano.le y2 y4)) \/ (y4 = (Nat.add y2 (y3 y4)))) y0 y1.
Definition term310 (x0 : type1586) := forall y0 : nat, exists y1 : nat -> nat, x0 y0 y1.
Definition term309 := forall y0 : nat, exists y1 : nat -> nat, forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2))).
Definition term287 (x0 : nat) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (Peano.le x0 y2)) \/ (y2 = (Nat.add x0 y3))) y0 y1.
Definition term285 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term282 (x0 : nat) := forall y0 : nat, exists y1 : nat, (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1)).
Definition term231 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0).
Definition term482 (x0 : type1605) := (fun y0 : type1605 => (~ ((forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2) = (forall y1 : nat, forall y2 : nat, y0 y1 (Nat.add y1 y2)))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) = (exists y3 : nat, y2 = (Nat.add y1 y3))) -> False) x0.
Definition term5 (x0 : type1605) := (~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False.
Definition term272 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.add x1 y1)) y0.
Definition term278 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.le x1 x0)) \/ ((fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term281 (x0 : nat) := fun y0 : nat => exists y1 : nat, (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1)).
Definition term194 (x0 : type1605) := fun y0 : nat => exists y1 : nat, ((forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1)))) \/ (((Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y2 : nat, forall y3 : nat, x0 y2 (Nat.add y2 y3))).
Definition term492 (x0 : type1605) (x1 : nat) := fun y0 : nat => ((Peano.le x1 y0) /\ (x0 x1 y0)) -> x0 x1 (S y0).
Definition term187 (x0 : nat) (x1 : nat) (x2 : type1605) := ((forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x2 y0 y1)) /\ (~ (x2 x0 (Nat.add x0 x1)))) \/ (((Peano.le x0 x1) /\ (~ (x2 x0 x1))) /\ (forall y0 : nat, forall y1 : nat, x2 y0 (Nat.add y0 y1))).
Definition term167 (x0 : type1605) (x1 : nat) := or (exists y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ (~ (x0 x1 (Nat.add x1 y0)))).
Definition term479 (x0 : type1606) (x1 : type1605) (x2 : nat) (x3 : nat) := ((x2 = x2) /\ (((Nat.add x2 (x0 x2 x3)) = x3) /\ (x1 x2 (Nat.add x2 (x0 x2 x3))))) -> x1 x2 x3.
Definition term437 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term385 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (~ (x0 = (Nat.add x1 x2)))).
Definition term18 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term526 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, (x0 y0 (Nat.add y0 y1)) -> x0 y0 (S (Nat.add y0 y1))) -> forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1).
Definition term525 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (x0 y0 y1)) -> x0 y0 (S y1)) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1.
Definition term169 (x0 : nat) (x1 : type1605) := (exists y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x1 y1 y2)) /\ (~ (x1 x0 (Nat.add x0 y0)))) \/ (exists y0 : nat, ((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2))).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term213 (x0 : nat) (x1 : nat) := ((Peano.le x1 x0) \/ (~ (exists y0 : nat, x0 = (Nat.add x1 y0)))) /\ ((~ (Peano.le x1 x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term338 (x0 : type1606) := (fun y0 : type1606 => forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2)))) x0.
Definition term7 (x0 : type1605) := (((~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False) -> (~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False) -> (~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False.
Definition term418 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq Prop ((x2 = (Nat.add x1 (x0 x1 x2))) \/ (~ (Peano.le x1 x2))).
Definition term101 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (x0 x1 (Nat.add x1 y0))) x2.
Definition term351 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term331 := fun y0 : type1606 => forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2))).
Definition term413 (x0 : nat) := ~ (x0 = x0).
Definition term84 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term34 (x0 : type1605) (x1 : nat) (x2 : nat) := (Peano.le x1 x2) /\ (~ (x0 x1 x2)).
Definition term246 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0).
Definition term224 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0).
Definition term557 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term344 (x0 : type1606) := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (y1 = (Nat.add y0 (x0 y0 y1)))).
Definition term264 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term442 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term67 (x0 : type1605) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, x0 y0 (Nat.add y0 y1)) x1).
Definition term50 (x0 : type1605) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) x1).
Definition term44 (x0 : type1605) (x1 : nat) := exists y0 : nat, (Peano.le x1 y0) /\ (~ (x0 x1 y0)).
Definition term239 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0.
Definition term234 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0.
Definition term95 (x0 : type1605) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (exists y0 : nat, ~ (x0 x1 (Nat.add x1 y0))).
Definition term386 (x0 : nat) (x1 : nat) (x2 : nat) := imp (x0 = (Nat.add x1 x2)).
Definition term40 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 y0) -> x0 x1 y0) x2.
Definition term485 (x0 : type1605) := ((forall y0 : nat, x0 y0 y0) /\ (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (x0 y0 y1)) -> x0 y0 (S y1))) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1.
Definition term191 (x0 : nat) (x1 : type1605) := (fun y0 : Prop => y0 = (exists y1 : nat, ((forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x1 y2 y3)) /\ (~ (x1 x0 (Nat.add x0 y1)))) \/ (((Peano.le x0 y1) /\ (~ (x1 x0 y1))) /\ (forall y2 : nat, forall y3 : nat, x1 y2 (Nat.add y2 y3))))) ((exists y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x1 y1 y2)) /\ (~ (x1 x0 (Nat.add x0 y0)))) \/ (exists y0 : nat, ((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2)))).
Definition term550 (x0 : type1605) (x1 : nat) := forall y0 : nat, (fun y1 : nat => x0 x1 (Nat.add x1 y1)) y0.
Definition term240 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0.
Definition term235 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0.
Definition term143 (x0 : nat) (x1 : nat) (x2 : type1605) := ((fun y0 : nat => (Peano.le x0 y0) /\ (~ (x2 x0 y0))) x1) /\ (forall y0 : nat, forall y1 : nat, x2 y0 (Nat.add y0 y1)).
Definition term334 (x0 : Prop) (x1 : type961) := x0 /\ (exists y0 : type1606, x1 y0).
Definition term268 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term504 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (x0 y0 y1) -> x0 y0 (S y1)) x1 x2.
Definition term291 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1))) x1 x2.
Definition term135 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 y0) /\ (~ (x0 x1 y0))) x2.
Definition term236 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1))).
Definition term134 (x0 : nat) (x1 : type1605) := exists y0 : nat, ((fun y1 : nat => (Peano.le x0 y1) /\ (~ (x1 x0 y1))) y0) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2)).
Definition term119 (x0 : type1605) := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (Peano.le y1 y2) /\ (~ (x0 y1 y2))) y0) /\ (forall y1 : nat, forall y2 : nat, x0 y1 (Nat.add y1 y2)).
Definition term545 (x0 : type1605) (x1 : nat) := ((fun y0 : nat => x0 x1 (Nat.add x1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => x0 x1 (Nat.add x1 y1)) y0) -> (fun y1 : nat => x0 x1 (Nat.add x1 y1)) (S y0)).
Definition term22 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term493 (x0 : type1605) (x1 : nat) := fun y0 : nat => (Peano.le x1 y0) -> (x0 x1 y0) -> x0 x1 (S y0).
Definition term454 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 x1 x2)) \/ (~ (x2 = x3)).
Definition term381 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term221 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term440 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term527 (x0 : type1605) := imp (forall y0 : nat, x0 y0 y0).
Definition term347 := exists y0 : type1606, (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2)))).
Definition term27 (x0 : type1605) := fun y0 : nat => forall y1 : nat, x0 y0 (Nat.add y0 y1).
Definition term56 (x0 : type1605) (x1 : nat) := ~ (forall y0 : nat, x0 x1 (Nat.add x1 y0)).
Definition term38 (x0 : type1605) (x1 : nat) := ~ (forall y0 : nat, (Peano.le x1 y0) -> x0 x1 y0).
Definition term212 (x0 : nat) (x1 : nat) := and ((Peano.le x1 x0) \/ (forall y0 : nat, ~ (x0 = (Nat.add x1 y0)))).
Definition term243 := fun y0 : nat => (forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term400 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (x0 x1 (Nat.add x1 x2))) -> x0 x1 (Nat.add x1 x2).
Definition term214 (x0 : nat) (x1 : nat) := ((Peano.le x1 x0) \/ (forall y0 : nat, ~ (x0 = (Nat.add x1 y0)))) /\ ((~ (Peano.le x1 x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term64 (x0 : type1605) := ~ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)).
Definition term47 (x0 : type1605) := ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1).
Definition term10 := ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term554 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term83 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term362 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) \/ (~ (x0 = (Nat.add x1 x2))).
Definition term416 (x0 : type1606) (x1 : nat) (x2 : nat) := Nat.add x1 (x0 x1 x2).
Definition term129 (x0 : nat) (x1 : type1605) := (exists y0 : nat, (Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y0 : nat, forall y1 : nat, x1 y0 (Nat.add y0 y1)).
Definition term549 (x0 : type1605) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 x1 (Nat.add x1 y1)) y0.
Definition term398 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term380 (x0 : Prop) := (~ x0) -> x0.
Definition term441 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term446 (x0 : type1606) (x1 : nat) (x2 : nat) := ((x2 = (Nat.add x1 (x0 x1 x2))) /\ (x2 = x2)) -> (Nat.add x1 (x0 x1 x2)) = x2.
Definition term530 (x0 : type1605) (x1 : nat) := (((fun y0 : nat => x0 x1 (Nat.add x1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => x0 x1 (Nat.add x1 y1)) y0) -> (fun y1 : nat => x0 x1 (Nat.add x1 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => x0 x1 (Nat.add x1 y1)) y0.
Definition term190 (x0 : nat) (x1 : type1605) := exists y0 : nat, ((forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x1 y1 y2)) /\ (~ (x1 x0 (Nat.add x0 y0)))) \/ (((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2))).
Definition term209 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (~ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term227 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) x1.
Definition term365 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) \/ (~ (x0 = (Nat.add x1 y0))).
Definition term60 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (x0 x1 (Nat.add x1 x2)).
Definition term433 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term376 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x1 y0)) \/ (y0 = (Nat.add x1 (x0 x1 y0)))) x2.
Definition term532 (x0 : type1605) (x1 : nat) := x0 x1 (Nat.add x1 (NUMERAL 0)).
Definition term565 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 x1 (Nat.add x1 y0)) -> x0 x1 (S (Nat.add x1 y0))) x2.
Definition term478 (x0 : type1605) (x1 : type1606) (x2 : nat) (x3 : nat) := (x2 = x2) /\ (((Nat.add x2 (x1 x2 x3)) = x3) /\ (x0 x2 (Nat.add x2 (x1 x2 x3)))).
Definition term435 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term275 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term274 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ (exists y0 : nat, (fun y1 : nat => x0 = (Nat.add x1 y1)) y0)).
Definition term412 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term111 (x0 : type1605) := fun y0 : nat => exists y1 : nat, (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1))).
Definition term52 (x0 : type1605) := fun y0 : nat => exists y1 : nat, (Peano.le y0 y1) /\ (~ (x0 y0 y1)).
Definition term356 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (x0 = (Nat.add x1 y0))) x2.
Definition term529 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term283 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term430 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term414 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term81 (x0 : type1605) := ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) /\ (~ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) \/ ((~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) /\ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1))).
Definition term138 (x0 : type1605) (x1 : nat) := and (exists y0 : nat, (fun y1 : nat => (Peano.le x1 y1) /\ (~ (x0 x1 y1))) y0).
Definition term123 (x0 : type1605) := and (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.le y1 y2) /\ (~ (x0 y1 y2))) y0).
Definition term301 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 y2))) y0 (x1 y0).
Definition term471 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (~ (x0 x1 x2)).
Definition term255 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2)))).
Definition term254 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0)).
Definition term233 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) /\ ((~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1)))).
Definition term232 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0) /\ ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (exists y2 : nat, y1 = (Nat.add x0 y2))) y0)).
Definition term547 (x0 : type1605) (x1 : nat) := imp (((fun y0 : nat => x0 x1 (Nat.add x1 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => x0 x1 (Nat.add x1 y1)) y0) -> (fun y1 : nat => x0 x1 (Nat.add x1 y1)) (S y0))).
Definition term96 (x0 : type1605) := fun y0 : nat => (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ ((fun y1 : nat => exists y2 : nat, ~ (x0 y1 (Nat.add y1 y2))) y0).
Definition term431 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term313 := exists y0 : type1606, forall y1 : nat, (fun y2 : nat => fun y3 : nat -> nat => forall y4 : nat, (~ (Peano.le y2 y4)) \/ (y4 = (Nat.add y2 (y3 y4)))) y1 (y0 y1).
Definition term311 (x0 : type1586) := exists y0 : type1606, forall y1 : nat, x0 y1 (y0 y1).
Definition term307 (x0 : nat) := exists y0 : nat -> nat, forall y1 : nat, (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 (y0 y1))).
Definition term288 (x0 : nat) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (Peano.le x0 y2)) \/ (y2 = (Nat.add x0 y3))) y1 (y0 y1).
Definition term286 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term318 (x0 : nat) := fun y0 : nat -> nat => (fun y1 : nat => fun y2 : nat -> nat => forall y3 : nat, (~ (Peano.le y1 y3)) \/ (y3 = (Nat.add y1 (y2 y3)))) x0 y0.
Definition term289 (x0 : nat) := fun y0 : nat => fun y1 : nat => (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1)).
Definition term276 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ ((fun y0 : nat => x0 = (Nat.add x1 y0)) x2).
Definition term220 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term555 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term98 (x0 : type1605) := exists y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ (exists y1 : nat, ~ (x0 y0 (Nat.add y0 y1))).
Definition term458 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) (x4 : nat) := (x1 x0 x4) \/ ((~ (x2 = x0)) \/ ((~ (x1 x2 x3)) \/ (~ (x3 = x4)))).
Definition term162 (x0 : type1605) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((Peano.le y1 y2) /\ (~ (x0 y1 y2))) /\ (forall y3 : nat, forall y4 : nat, x0 y3 (Nat.add y3 y4))) y0.
Definition term158 (x0 : type1605) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) \/ (x0 y3 y4)) /\ (~ (x0 y1 (Nat.add y1 y2)))) y0.
Definition term121 (x0 : type1605) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (Peano.le y1 y2) /\ (~ (x0 y1 y2))) y0.
Definition term90 (x0 : type1605) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ~ (x0 y1 (Nat.add y1 y2))) y0.
Definition term352 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (forall y0 : nat, x1 y0).
Definition term193 (x0 : nat) (x1 : type1605) := @eq Prop (((exists y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x1 y1 y2)) /\ (~ (x1 x0 (Nat.add x0 y0)))) \/ (exists y0 : nat, ((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2)))) = (exists y0 : nat, ((forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x1 y1 y2)) /\ (~ (x1 x0 (Nat.add x0 y0)))) \/ (((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2))))).
Definition term460 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (~ (x0 x1 x3)) \/ ((~ (x1 = x2)) \/ (~ (x3 = x4))).
Definition term428 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term302 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 (x1 y0))).
Definition term551 (x0 : type1605) (x1 : nat) := ((x0 x1 (Nat.add x1 (NUMERAL 0))) /\ (forall y0 : nat, (x0 x1 (Nat.add x1 y0)) -> x0 x1 (Nat.add x1 (S y0)))) -> forall y0 : nat, x0 x1 (Nat.add x1 y0).
Definition term564 (x0 : type1605) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (x0 y0 (Nat.add y0 y1)) -> x0 y0 (S (Nat.add y0 y1))) x1.
Definition term375 (x0 : type1606) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (y1 = (Nat.add y0 (x0 y0 y1)))) x1.
Definition term373 (x0 : type1605) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) x1.
Definition term371 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) \/ (~ (y0 = (Nat.add x0 y1)))) x1.
Definition term66 (x0 : type1605) (x1 : nat) := (fun y0 : nat => forall y1 : nat, x0 y0 (Nat.add y0 y1)) x1.
Definition term49 (x0 : type1605) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) x1.
Definition term540 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 (Nat.add x1 x2)) -> x0 x1 (Nat.add x1 (S x2)).
Definition term461 (x0 : type1605) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (x0 x2 x4) \/ ((~ (x0 x1 x3)) \/ ((~ (x1 = x2)) \/ (~ (x3 = x4)))).
Definition term200 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 = (Nat.add x1 y0)) x2.
Definition term74 (x0 : type1605) := (exists y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)).
Definition term538 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 x1 (Nat.add x1 (S x2)).
Definition term543 (x0 : type1605) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => x0 x1 (Nat.add x1 y1)) y0) -> (fun y1 : nat => x0 x1 (Nat.add x1 y1)) (S y0).
Definition term335 (x0 : Prop) (x1 : type961) := exists y0 : type1606, x0 /\ (x1 y0).
Definition term333 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (exists y0 : type1606, forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2)))).
Definition term510 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> (fun y2 : nat => fun y3 : nat => (x0 y2 y3) -> x0 y2 (S y3)) y0 y1.
Definition term54 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1).
Definition term31 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1.
Definition term110 (x0 : type1605) (x1 : nat) := exists y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ (~ (x0 x1 (Nat.add x1 y0))).
Definition term241 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term317 (x0 : nat) (x1 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat, (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 (y0 y1)))) x1.
Definition term300 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (x2 = (Nat.add x0 (x1 x2))).
Definition term515 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 (Nat.add x1 x2)) -> x0 x1 (S (Nat.add x1 x2)).
Definition term328 (x0 : type1606) := forall y0 : nat, (fun y1 : nat => fun y2 : nat -> nat => forall y3 : nat, (~ (Peano.le y1 y3)) \/ (y3 = (Nat.add y1 (y2 y3)))) y0 (x0 y0).
Definition term390 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 (Nat.add x0 x1))) -> Peano.le x0 (Nat.add x0 x1).
Definition term14 := fun y0 : type1605 => (~ ((forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2) = (forall y1 : nat, forall y2 : nat, y0 y1 (Nat.add y1 y2)))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) = (exists y3 : nat, y2 = (Nat.add y1 y3))) -> False.
Definition term103 (x0 : type1605) (x1 : nat) := exists y0 : nat, (fun y1 : nat => ~ (x0 x1 (Nat.add x1 y1))) y0.
Definition term86 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term553 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term17 := forall y0 : type1605, (~ ((forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2) = (forall y1 : nat, forall y2 : nat, y0 y1 (Nat.add y1 y2)))) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) = (exists y3 : nat, y2 = (Nat.add y1 y3))).
Definition term179 (x0 : nat) (x1 : type1605) (x2 : nat) := (fun y0 : nat => ((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2))) x2.
Definition term411 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term293 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 y2))) x1 y0.
Definition term374 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x1 y0)) \/ (x0 x1 y0)) x2.
Definition term354 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (forall y0 : nat, (fun y1 : nat => ~ (x0 = (Nat.add x1 y1))) y0).
Definition term325 (x0 : type1606) (x1 : nat) := forall y0 : nat, (~ (Peano.le x1 y0)) \/ (y0 = (Nat.add x1 (x0 x1 y0))).
Definition term304 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 (x1 y0))).
Definition term476 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := ((x0 = x3) /\ ((x1 = x4) /\ (x2 x0 x1))) -> x2 x3 x4.
Definition term533 (x0 : type1605) (x1 : nat) := and ((fun y0 : nat => x0 x1 (Nat.add x1 y0)) (NUMERAL 0)).
Definition term271 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term208 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term429 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term393 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x2)) \/ (x0 x1 x2)).
Definition term85 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term16 := forall y0 : type1605, (~ ((forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2) = (forall y1 : nat, forall y2 : nat, y0 y1 (Nat.add y1 y2)))) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) = (exists y3 : nat, y2 = (Nat.add y1 y3))) -> False.
Definition term387 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = (Nat.add x1 x0)) -> Peano.le x1 x2.
Definition term173 (x0 : nat) (x1 : type1605) := (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x1 y2 y3)) /\ (~ (x1 x0 (Nat.add x0 y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => ((Peano.le x0 y1) /\ (~ (x1 x0 y1))) /\ (forall y2 : nat, forall y3 : nat, x1 y2 (Nat.add y2 y3))) y0).
Definition term155 (x0 : type1605) := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) \/ (x0 y3 y4)) /\ (~ (x0 y1 (Nat.add y1 y2)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Peano.le y1 y2) /\ (~ (x0 y1 y2))) /\ (forall y3 : nat, forall y4 : nat, x0 y3 (Nat.add y3 y4))) y0).
Definition term185 (x0 : type1605) (x1 : nat) (x2 : nat) := or ((forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (~ (x0 x1 (Nat.add x1 x2)))).
Definition term9 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False.
Definition term506 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 x2) -> x0 x1 (S x2).
Definition term372 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) \/ (~ (x0 = (Nat.add x1 y0)))) x2.
Definition term465 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (x2 x0 x1) \/ ((~ (x3 = x0)) \/ ((~ (x4 = x1)) \/ (~ (x2 x3 x4)))).
Definition term292 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x1 x0)) \/ (x0 = (Nat.add x1 y0))) x2.
Definition term176 (x0 : type1605) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 x1 (Nat.add x1 y1)))) y0.
Definition term136 (x0 : type1605) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x1 y1) /\ (~ (x0 x1 y1))) y0.
Definition term330 := fun y0 : type1606 => forall y1 : nat, (fun y2 : nat => fun y3 : nat -> nat => forall y4 : nat, (~ (Peano.le y2 y4)) \/ (y4 = (Nat.add y2 (y3 y4)))) y1 (y0 y1).
Definition term306 (x0 : nat) := fun y0 : nat -> nat => forall y1 : nat, (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 (y0 y1))).
Definition term305 (x0 : nat) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (Peano.le x0 y2)) \/ (y2 = (Nat.add x0 y3))) y1 (y0 y1).
Definition term340 := exists y0 : type1606, (fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0.
Definition term502 (x0 : type1605) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (x0 y0 y1) -> x0 y0 (S y1)) x1.
Definition term80 (x0 : type1605) := or ((forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (exists y0 : nat, exists y1 : nat, ~ (x0 y0 (Nat.add y0 y1)))).
Definition term456 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) (x4 : nat) := (x1 x0 x4) \/ ((~ (x1 x2 x3)) \/ (~ (x3 = x4))).
Definition term512 (x0 : type1605) := @eq Prop (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (x0 y0 y1) -> x0 y0 (S y1)).
Definition term511 (x0 : type1605) := @eq Prop (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (fun y2 : nat => fun y3 : nat => (x0 y2 y3) -> x0 y2 (S y3)) y0 y1).
Definition term322 := @eq Prop (forall y0 : nat, exists y1 : nat -> nat, forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2)))).
Definition term321 := @eq Prop (forall y0 : nat, exists y1 : nat -> nat, (fun y2 : nat => fun y3 : nat -> nat => forall y4 : nat, (~ (Peano.le y2 y4)) \/ (y4 = (Nat.add y2 (y3 y4)))) y0 y1).
Definition term297 (x0 : nat) := @eq Prop (forall y0 : nat, exists y1 : nat, (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1))).
Definition term296 (x0 : nat) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (Peano.le x0 y2)) \/ (y2 = (Nat.add x0 y3))) y0 y1).
Definition term32 (x0 : type1605) := @eq Prop (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1).
Definition term238 (x0 : nat) := and (forall y0 : nat, (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))).
Definition term215 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) /\ ((~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))).
Definition term69 (x0 : type1605) := fun y0 : nat => exists y1 : nat, ~ (x0 y0 (Nat.add y0 y1)).
Definition term541 (x0 : type1605) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => x0 x1 (Nat.add x1 y1)) y0) -> (fun y1 : nat => x0 x1 (Nat.add x1 y1)) (S y0).
Definition term516 (x0 : type1605) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (x0 y1 y2) -> x0 y1 (S y2)) x1 (Nat.add x1 y0).
Definition term405 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (x2 x0 x1) \/ (~ (x2 x3 x4)).
Definition term19 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term528 (x0 : type1605) := (forall y0 : nat, x0 y0 y0) -> (forall y0 : nat, forall y1 : nat, (x0 y0 (Nat.add y0 y1)) -> x0 y0 (S (Nat.add y0 y1))) -> forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1).
Definition term486 (x0 : type1605) := (forall y0 : nat, x0 y0 y0) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (x0 y0 y1)) -> x0 y0 (S y1)) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1.
Definition term58 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 x1 (Nat.add x1 y0)) x2.
Definition term563 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term361 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) \/ ((fun y0 : nat => ~ (x0 = (Nat.add x1 y0))) x2).
Definition term266 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term339 := fun y0 : type1606 => (fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0.
Definition term128 (x0 : nat) (x1 : type1605) := ((fun y0 : nat => exists y1 : nat, (Peano.le y0 y1) /\ (~ (x1 y0 y1))) x0) /\ (forall y0 : nat, forall y1 : nat, x1 y0 (Nat.add y0 y1)).
Definition term166 (x0 : type1605) (x1 : nat) := or ((fun y0 : nat => exists y1 : nat, (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1)))) x1).
Definition term45 (x0 : type1605) (x1 : nat) := fun y0 : nat => (~ (Peano.le x1 y0)) \/ (x0 x1 y0).
Definition term434 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term106 (x0 : type1605) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ ((fun y0 : nat => ~ (x0 x1 (Nat.add x1 y0))) x2).
Definition term161 (x0 : type1605) (x1 : nat) := (fun y0 : nat => exists y1 : nat, ((Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y2 : nat, forall y3 : nat, x0 y2 (Nat.add y2 y3))) x1.
Definition term157 (x0 : type1605) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1)))) x1.
Definition term120 (x0 : type1605) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (Peano.le y0 y1) /\ (~ (x0 y0 y1))) x1.
Definition term558 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term522 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (x0 y0 (Nat.add y0 y1)) -> x0 y0 (S (Nat.add y0 y1)).
Definition term500 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (x0 y2 y3) -> x0 y2 (S y3)) y0 (Nat.add y0 y1).
Definition term499 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (fun y2 : nat => fun y3 : nat => (x0 y2 y3) -> x0 y2 (S y3)) y0 y1.
Definition term498 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (x0 y0 y1) -> x0 y0 (S y1).
Definition term488 (x0 : type1605) := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (x0 y0 y1)) -> x0 y0 (S y1).
Definition term369 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) \/ (~ (y1 = (Nat.add y0 y2))).
Definition term367 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) \/ (~ (y0 = (Nat.add x0 y1))).
Definition term329 (x0 : type1606) := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (y1 = (Nat.add y0 (x0 y0 y1))).
Definition term263 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2)).
Definition term258 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2))).
Definition term218 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ ((~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term55 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1).
Definition term11 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2)).
Definition term2 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1).
Definition term1 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1.
Definition term94 (x0 : type1605) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ ((fun y0 : nat => exists y1 : nat, ~ (x0 y0 (Nat.add y0 y1))) x1).
Definition term265 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term82 (x0 : type1605) := ((forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (exists y0 : nat, exists y1 : nat, ~ (x0 y0 (Nat.add y0 y1)))) \/ ((exists y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1))).
Definition term201 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => x0 = (Nat.add x1 y0)) x2).
Definition term59 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => x0 x1 (Nat.add x1 y0)) x2).
Definition term41 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (Peano.le x1 y0) -> x0 x1 y0) x2).
Definition term466 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (~ ((~ (x0 = x3)) \/ ((~ (x1 = x4)) \/ (~ (x2 x0 x1))))) -> x2 x3 x4.
Definition term252 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))) x0).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term196 (x0 : nat -> Prop) := ~ (ex x0).
Definition term226 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term270 (x0 : nat) (x1 : nat) := exists y0 : nat, (~ (Peano.le x1 x0)) \/ ((fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term97 (x0 : type1605) := fun y0 : nat => (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ (exists y1 : nat, ~ (x0 y0 (Nat.add y0 y1))).
Definition term172 (x0 : type1605) := exists y0 : nat, (exists y1 : nat, (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1)))) \/ (exists y1 : nat, ((Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y2 : nat, forall y3 : nat, x0 y2 (Nat.add y2 y3))).
Definition term421 (x0 : type1606) (x1 : nat) (x2 : nat) := (~ (x2 = (Nat.add x1 (x0 x1 x2)))) -> x2 = (Nat.add x1 (x0 x1 x2)).
Definition term248 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2)).
Definition term247 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2))).
Definition term23 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2)).
Definition term174 (x0 : nat) (x1 : type1605) := exists y0 : nat, ((fun y1 : nat => (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x1 y2 y3)) /\ (~ (x1 x0 (Nat.add x0 y1)))) y0) \/ ((fun y1 : nat => ((Peano.le x0 y1) /\ (~ (x1 x0 y1))) /\ (forall y2 : nat, forall y3 : nat, x1 y2 (Nat.add y2 y3))) y0).
Definition term156 (x0 : type1605) := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) \/ (x0 y3 y4)) /\ (~ (x0 y1 (Nat.add y1 y2)))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((Peano.le y1 y2) /\ (~ (x0 y1 y2))) /\ (forall y3 : nat, forall y4 : nat, x0 y3 (Nat.add y3 y4))) y0).
Definition term319 (x0 : nat) := exists y0 : nat -> nat, (fun y1 : nat => fun y2 : nat -> nat => forall y3 : nat, (~ (Peano.le y1 y3)) \/ (y3 = (Nat.add y1 (y2 y3)))) x0 y0.
Definition term346 := fun y0 : type1606 => (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2)))).
Definition term503 (x0 : type1605) (x1 : nat) := fun y0 : nat => (x0 x1 y0) -> x0 x1 (S y0).
Definition term28 (x0 : type1605) (x1 : nat) (x2 : nat) := (Peano.le x1 x2) -> x0 x1 x2.
Definition term320 := fun y0 : nat => exists y1 : nat -> nat, (fun y2 : nat => fun y3 : nat -> nat => forall y4 : nat, (~ (Peano.le y2 y4)) \/ (y4 = (Nat.add y2 (y3 y4)))) y0 y1.
Definition term144 (x0 : nat) (x1 : nat) (x2 : type1605) := ((Peano.le x0 x1) /\ (~ (x2 x0 x1))) /\ (forall y0 : nat, forall y1 : nat, x2 y0 (Nat.add y0 y1)).
Definition term379 (x0 : nat) (x1 : nat) := ~ ((Nat.add x0 x1) = (Nat.add x0 x1)).
Definition term197 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term355 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) \/ ((fun y1 : nat => ~ (x0 = (Nat.add x1 y1))) y0).
Definition term363 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x1 x0) \/ ((fun y1 : nat => ~ (x0 = (Nat.add x1 y1))) y0).
Definition term420 (x0 : type1606) (x1 : nat) (x2 : nat) := (Peano.le x1 x2) -> x2 = (Nat.add x1 (x0 x1 x2)).
Definition term448 (x0 : type1606) (x1 : nat) (x2 : nat) := ~ ((Nat.add x1 (x0 x1 x2)) = x2).
Definition term308 := fun y0 : nat => exists y1 : nat -> nat, forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2))).
Definition term269 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (exists y0 : nat, (fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term132 (x0 : type1605) := exists y0 : nat, (exists y1 : nat, (Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y1 : nat, forall y2 : nat, x0 y1 (Nat.add y1 y2)).
Definition term424 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term467 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := ~ ((~ (x3 = x0)) \/ ((~ (x4 = x1)) \/ (~ (x2 x3 x4)))).
Definition term168 (x0 : type1605) (x1 : nat) := ((fun y0 : nat => exists y1 : nat, (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1)))) x1) \/ ((fun y0 : nat => exists y1 : nat, ((Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y2 : nat, forall y3 : nat, x0 y2 (Nat.add y2 y3))) x1).
Definition term225 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1))).
Definition term113 (x0 : type1605) := or (exists y0 : nat, exists y1 : nat, (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1)))).
Definition term26 (x0 : type1605) (x1 : nat) := forall y0 : nat, x0 x1 (Nat.add x1 y0).
Definition term401 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 (Nat.add x1 x2)) -> False.
Definition term117 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term99 (x0 : type1605) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (exists y0 : nat, (fun y1 : nat => ~ (x0 x1 (Nat.add x1 y1))) y0).
Definition term87 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ~ (x0 y1 (Nat.add y1 y2))) y0).
Definition term145 (x0 : nat) (x1 : type1605) := fun y0 : nat => ((fun y1 : nat => (Peano.le x0 y1) /\ (~ (x1 x0 y1))) y0) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2)).
Definition term130 (x0 : type1605) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (Peano.le y1 y2) /\ (~ (x0 y1 y2))) y0) /\ (forall y1 : nat, forall y2 : nat, x0 y1 (Nat.add y1 y2)).
Definition term513 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (x0 y0 y1) -> x0 y0 (S y1)) x1 (Nat.add x1 x2).
Definition term68 (x0 : type1605) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, x0 y1 (Nat.add y1 y2)) y0).
Definition term51 (x0 : type1605) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) -> x0 y1 y2) y0).
Definition term46 (x0 : type1605) (x1 : nat) := forall y0 : nat, (~ (Peano.le x1 y0)) \/ (x0 x1 y0).
Definition term131 (x0 : type1605) := fun y0 : nat => (exists y1 : nat, (Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y1 : nat, forall y2 : nat, x0 y1 (Nat.add y1 y2)).
Definition term294 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 y2))) x1 y0.
Definition term452 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (x2 x0 x1) \/ ((~ (x4 = x1)) \/ (~ (x2 x3 x4))).
Definition term230 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) x1) /\ ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))) x1).
Definition term222 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term427 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term20 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term273 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.add x1 y1)) y0.
Definition term181 (x0 : nat) (x1 : type1605) := exists y0 : nat, (fun y1 : nat => ((Peano.le x0 y1) /\ (~ (x1 x0 y1))) /\ (forall y2 : nat, forall y3 : nat, x1 y2 (Nat.add y2 y3))) y0.
Definition term177 (x0 : type1605) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 x1 (Nat.add x1 y1)))) y0.
Definition term137 (x0 : type1605) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (Peano.le x1 y1) /\ (~ (x0 x1 y1))) y0.
Definition term377 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (x0 x1 x2).
Definition term348 (x0 : type1606) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x2)) \/ (x2 = (Nat.add x1 (x0 x1 x2))).
Definition term561 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term24 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 x1 (Nat.add x1 x2).
Definition term483 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term314 := fun y0 : nat => fun y1 : nat -> nat => forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2))).
Definition term534 (x0 : type1605) (x1 : nat) := and (x0 x1 (Nat.add x1 (NUMERAL 0))).
Definition term126 (x0 : type1605) (x1 : nat) := and ((fun y0 : nat => exists y1 : nat, (Peano.le y0 y1) /\ (~ (x0 y0 y1))) x1).
Definition term439 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term337 := exists y0 : type1606, (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) /\ ((fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0).
Definition term552 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term205 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ (x0 = (Nat.add x1 y0)).
Definition term568 := forall y0 : type1605, ((forall y1 : nat, y0 y1 y1) /\ (forall y1 : nat, forall y2 : nat, ((Peano.le y1 y2) /\ (y0 y1 y2)) -> y0 y1 (S y2))) -> forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2.
Definition term206 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term62 (x0 : type1605) (x1 : nat) := fun y0 : nat => ~ (x0 x1 (Nat.add x1 y0)).
Definition term455 (x0 : type1605) (x1 : nat) (x2 : nat) := or (x0 x1 x2).
Definition term544 (x0 : type1605) (x1 : nat) := forall y0 : nat, (x0 x1 (Nat.add x1 y0)) -> x0 x1 (Nat.add x1 (S y0)).
Definition term171 (x0 : type1605) := fun y0 : nat => (exists y1 : nat, (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1)))) \/ (exists y1 : nat, ((Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y2 : nat, forall y3 : nat, x0 y2 (Nat.add y2 y3))).
Definition term505 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 x1 y0) -> x0 x1 (S y0)) x2.
Definition term403 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term409 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (x3 = x0) -> (~ (x4 = x1)) \/ ((x2 x0 x1) \/ (~ (x2 x3 x4))).
Definition term242 (x0 : nat) := (forall y0 : nat, (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) /\ (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))).
Definition term290 (x0 : nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (~ (Peano.le x0 y0)) \/ (y0 = (Nat.add x0 y1))) x1.
Definition term378 (x0 : nat) (x1 : nat) := (~ ((Nat.add x0 x1) = (Nat.add x0 x1))) -> (Nat.add x0 x1) = (Nat.add x0 x1).
Definition term477 (x0 : type1605) (x1 : type1606) (x2 : nat) (x3 : nat) := ((Nat.add x2 (x1 x2 x3)) = x3) /\ (x0 x2 (Nat.add x2 (x1 x2 x3))).
Definition term133 (x0 : nat) (x1 : type1605) := (exists y0 : nat, (fun y1 : nat => (Peano.le x0 y1) /\ (~ (x1 x0 y1))) y0) /\ (forall y0 : nat, forall y1 : nat, x1 y0 (Nat.add y0 y1)).
Definition term118 (x0 : type1605) := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.le y1 y2) /\ (~ (x0 y1 y2))) y0) /\ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)).
Definition term260 := and (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))).
Definition term76 (x0 : type1605) := and (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)).
Definition term75 (x0 : type1605) := and (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1).
Definition term170 (x0 : type1605) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) \/ (x0 y3 y4)) /\ (~ (x0 y1 (Nat.add y1 y2)))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((Peano.le y1 y2) /\ (~ (x0 y1 y2))) /\ (forall y3 : nat, forall y4 : nat, x0 y3 (Nat.add y3 y4))) y0).
Definition term480 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (x0 x1 x2)) -> x0 x1 x2.
Definition term299 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x0 x2)) \/ (x2 = (Nat.add x0 y0))) (x1 x2).
Definition term116 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term489 (x0 : type1605) (x1 : nat) (x2 : nat) := ((Peano.le x1 x2) /\ (x0 x1 x2)) -> x0 x1 (S x2).
Definition term199 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term261 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0.
Definition term256 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0.
Definition term389 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term546 (x0 : type1605) (x1 : nat) := (x0 x1 (Nat.add x1 (NUMERAL 0))) /\ (forall y0 : nat, (x0 x1 (Nat.add x1 y0)) -> x0 x1 (Nat.add x1 (S y0))).
Definition term559 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term251 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term249 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) x0.
Definition term303 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (~ (Peano.le x0 y1)) \/ (y1 = (Nat.add x0 y2))) y0 (x1 y0).
Definition term520 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (x0 y2 y3) -> x0 y2 (S y3)) y0 (Nat.add y0 y1).
Definition term73 (x0 : type1605) := (~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) /\ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)).
Definition term449 (x0 : type1605) (x1 : type1606) (x2 : nat) (x3 : nat) := x0 x2 (Nat.add x2 (x1 x2 x3)).
Definition term336 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (exists y0 : type1606, (fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0).
Definition term108 (x0 : type1605) (x1 : nat) := fun y0 : nat => (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ ((fun y1 : nat => ~ (x0 x1 (Nat.add x1 y1))) y0).
Definition term6 (x0 : type1605) := ((~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False) -> (~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False.
Definition term396 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term315 (x0 : nat) := (fun y0 : nat => fun y1 : nat -> nat => forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2)))) x0.
Definition term360 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) \/ (forall y0 : nat, ~ (x0 = (Nat.add x1 y0)))).
Definition term359 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) \/ (forall y0 : nat, (fun y1 : nat => ~ (x0 = (Nat.add x1 y1))) y0)).
Definition term518 (x0 : type1605) (x1 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (x0 y1 y2) -> x0 y1 (S y2)) x1 (Nat.add x1 y0).
Definition term148 (x0 : type1605) := fun y0 : nat => exists y1 : nat, ((Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y2 : nat, forall y3 : nat, x0 y2 (Nat.add y2 y3)).
Definition term127 (x0 : type1605) (x1 : nat) := and (exists y0 : nat, (Peano.le x1 y0) /\ (~ (x0 x1 y0))).
Definition term399 (x0 : type1605) (x1 : nat) (x2 : nat) := (Peano.le x1 (Nat.add x1 x2)) -> x0 x1 (Nat.add x1 x2).
Definition term332 := exists y0 : type1606, forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2))).
Definition term207 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term79 (x0 : type1605) := or ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) /\ (~ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))).
Definition term210 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (forall y0 : nat, ~ (x0 = (Nat.add x1 y0))).
Definition term464 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (~ (x3 = x0)) \/ ((~ (x4 = x1)) \/ (~ (x2 x3 x4))).
Definition term459 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) (x4 : nat) := (~ (x2 = x0)) \/ ((~ (x1 x2 x3)) \/ (~ (x3 = x4))).
Definition term323 (x0 : type1606) (x1 : nat) := (fun y0 : nat => fun y1 : nat -> nat => forall y2 : nat, (~ (Peano.le y0 y2)) \/ (y2 = (Nat.add y0 (y1 y2)))) x1 (x0 x1).
Definition term395 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x2))) -> x0 x1 x2.
Definition term469 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := ~ ((~ (x3 = x0)) \/ (~ (x1 x2 x3))).
Definition term436 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term490 (x0 : type1605) (x1 : nat) (x2 : nat) := (Peano.le x1 x2) -> (x0 x1 x2) -> x0 x1 (S x2).
Definition term462 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := @eq Prop ((~ (x3 = x0)) \/ ((~ (x4 = x1)) \/ ((x2 x0 x1) \/ (~ (x2 x3 x4))))).
Definition term65 (x0 : type1605) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, x0 y1 (Nat.add y1 y2)) y0).
Definition term57 (x0 : type1605) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => x0 x1 (Nat.add x1 y1)) y0).
Definition term48 (x0 : type1605) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) -> x0 y1 y2) y0).
Definition term39 (x0 : type1605) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.le x1 y1) -> x0 x1 y1) y0).
Definition term475 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := imp ((x3 = x0) /\ ((x4 = x1) /\ (x2 x3 x4))).
Definition term562 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term184 (x0 : type1605) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ (~ (x0 x1 (Nat.add x1 y0)))) x2).
Definition term150 (x0 : type1605) := (exists y0 : nat, exists y1 : nat, (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1)))) \/ (exists y0 : nat, exists y1 : nat, ((Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y2 : nat, forall y3 : nat, x0 y2 (Nat.add y2 y3))).
Definition term353 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 \/ (x1 y0).
Definition term392 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 x2) \/ (~ (Peano.le x1 x2)).
Definition term295 (x0 : nat) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (Peano.le x0 y2)) \/ (y2 = (Nat.add x0 y3))) y0 y1.
Definition term109 (x0 : type1605) (x1 : nat) := fun y0 : nat => (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ (~ (x0 x1 (Nat.add x1 y0))).
Definition term259 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0).
Definition term237 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add x0 y2)))) y0).
Definition term324 (x0 : type1606) (x1 : nat) := (fun y0 : nat -> nat => forall y1 : nat, (~ (Peano.le x1 y1)) \/ (y1 = (Nat.add x1 (y0 y1)))) (x0 x1).
Definition term542 (x0 : type1605) (x1 : nat) := fun y0 : nat => (x0 x1 (Nat.add x1 y0)) -> x0 x1 (Nat.add x1 (S y0)).
Definition term407 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term468 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (~ (~ (x3 = x0))) /\ (~ ((~ (x4 = x1)) \/ (~ (x2 x3 x4)))).
Definition term250 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) x0).
Definition term13 (x0 : type1605) := (~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term357 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ~ (x0 = (Nat.add x1 y1))) y0.
Definition term102 (x0 : type1605) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ~ (x0 x1 (Nat.add x1 y1))) y0.
Definition term445 (x0 : type1606) (x1 : nat) (x2 : nat) := (x2 = (Nat.add x1 (x0 x1 x2))) /\ (x2 = x2).
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ (x0 = (Nat.add x1 x2)).
Definition term394 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x1 x2) \/ (~ (Peano.le x1 x2))).
Definition term71 (x0 : type1605) := and (~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)).
Definition term514 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 x1 y0) -> x0 x1 (S y0)) (Nat.add x1 x2).
Definition term229 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term472 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (x3 = x0) /\ (x1 x2 x3).
Definition term451 (x0 : type1605) (x1 : type1606) (x2 : nat) (x3 : nat) := ~ (x0 x2 (Nat.add x2 (x1 x2 x3))).
Definition term366 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) \/ (~ (y0 = (Nat.add x0 y1))).
Definition term453 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (~ (x3 = x0)) \/ (~ (x1 x2 x3)).
Definition term342 := @eq Prop ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (exists y0 : type1606, forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (y2 = (Nat.add y1 (y0 y1 y2))))).
Definition term341 := @eq Prop ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (exists y0 : type1606, (fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0)).
Definition term105 (x0 : type1605) (x1 : nat) := @eq Prop ((forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (exists y0 : nat, ~ (x0 x1 (Nat.add x1 y0)))).
Definition term104 (x0 : type1605) (x1 : nat) := @eq Prop ((forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (exists y0 : nat, (fun y1 : nat => ~ (x0 x1 (Nat.add x1 y1))) y0)).
Definition term93 (x0 : type1605) := @eq Prop ((forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (exists y0 : nat, exists y1 : nat, ~ (x0 y0 (Nat.add y0 y1)))).
Definition term92 (x0 : type1605) := @eq Prop ((forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ~ (x0 y1 (Nat.add y1 y2))) y0)).
Definition term443 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term219 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term508 (x0 : type1605) (x1 : nat) := fun y0 : nat => (Peano.le x1 y0) -> (fun y1 : nat => fun y2 : nat => (x0 y1 y2) -> x0 y1 (S y2)) x1 y0.
Definition term163 (x0 : type1605) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Peano.le y1 y2) /\ (~ (x0 y1 y2))) /\ (forall y3 : nat, forall y4 : nat, x0 y3 (Nat.add y3 y4))) y0.
Definition term159 (x0 : type1605) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) \/ (x0 y3 y4)) /\ (~ (x0 y1 (Nat.add y1 y2)))) y0.
Definition term122 (x0 : type1605) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.le y1 y2) /\ (~ (x0 y1 y2))) y0.
Definition term91 (x0 : type1605) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ~ (x0 y1 (Nat.add y1 y2))) y0.
Definition term195 (x0 : type1605) := exists y0 : nat, exists y1 : nat, ((forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1)))) \/ (((Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y2 : nat, forall y3 : nat, x0 y2 (Nat.add y2 y3))).
Definition term149 (x0 : type1605) := exists y0 : nat, exists y1 : nat, ((Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y2 : nat, forall y3 : nat, x0 y2 (Nat.add y2 y3)).
Definition term112 (x0 : type1605) := exists y0 : nat, exists y1 : nat, (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1))).
Definition term70 (x0 : type1605) := exists y0 : nat, exists y1 : nat, ~ (x0 y0 (Nat.add y0 y1)).
Definition term53 (x0 : type1605) := exists y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (~ (x0 y0 y1)).
Definition term531 (x0 : type1605) (x1 : nat) := (fun y0 : nat => x0 x1 (Nat.add x1 y0)) (NUMERAL 0).
Definition term244 := forall y0 : nat, (forall y1 : nat, (Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term147 (x0 : nat) (x1 : type1605) := exists y0 : nat, ((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2)).
Definition term417 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x2)) \/ (x2 = (Nat.add x1 (x0 x1 x2)))).
Definition term154 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term189 (x0 : nat) (x1 : type1605) := fun y0 : nat => ((forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x1 y1 y2)) /\ (~ (x1 x0 (Nat.add x0 y0)))) \/ (((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2))).
Definition term204 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ (x0 = (Nat.add x1 y0)).
Definition term228 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.le x0 y0) \/ (forall y1 : nat, ~ (y0 = (Nat.add x0 y1)))) x1).
Definition term203 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term61 (x0 : type1605) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 x1 (Nat.add x1 y1)) y0).
Definition term42 (x0 : type1605) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.le x1 y1) -> x0 x1 y1) y0).
Definition term140 (x0 : nat) (x1 : type1605) := @eq Prop ((exists y0 : nat, (Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y0 : nat, forall y1 : nat, x1 y0 (Nat.add y0 y1))).
Definition term139 (x0 : nat) (x1 : type1605) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (Peano.le x0 y1) /\ (~ (x1 x0 y1))) y0) /\ (forall y0 : nat, forall y1 : nat, x1 y0 (Nat.add y0 y1))).
Definition term125 (x0 : type1605) := @eq Prop ((exists y0 : nat, exists y1 : nat, (Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1))).
Definition term124 (x0 : type1605) := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.le y1 y2) /\ (~ (x0 y1 y2))) y0) /\ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1))).
Definition term539 (x0 : type1605) (x1 : nat) (x2 : nat) := ((fun y0 : nat => x0 x1 (Nat.add x1 y0)) x2) -> (fun y0 : nat => x0 x1 (Nat.add x1 y0)) (S x2).
Definition term509 (x0 : type1605) (x1 : nat) := forall y0 : nat, (Peano.le x1 y0) -> (fun y1 : nat => fun y2 : nat => (x0 y1 y2) -> x0 y1 (S y2)) x1 y0.
Definition term211 (x0 : nat) (x1 : nat) := and ((Peano.le x1 x0) \/ (~ (exists y0 : nat, x0 = (Nat.add x1 y0)))).
Definition term29 (x0 : type1605) (x1 : nat) := fun y0 : nat => (Peano.le x1 y0) -> x0 x1 y0.
Definition term280 (x0 : nat) (x1 : nat) := exists y0 : nat, (~ (Peano.le x1 x0)) \/ (x0 = (Nat.add x1 y0)).
Definition term535 (x0 : type1605) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => x0 x1 (Nat.add x1 y0)) x2).
Definition term567 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 (Nat.add x1 x2)) -> (x0 x1 (S (Nat.add x1 x2))) = True.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term423 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term188 (x0 : nat) (x1 : type1605) := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x1 y2 y3)) /\ (~ (x1 x0 (Nat.add x0 y1)))) y0) \/ ((fun y1 : nat => ((Peano.le x0 y1) /\ (~ (x1 x0 y1))) /\ (forall y2 : nat, forall y3 : nat, x1 y2 (Nat.add y2 y3))) y0).
Definition term3 (x0 : type1605) := (~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> False.
Definition term178 (x0 : type1605) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 x1 (Nat.add x1 y1)))) y0).
Definition term160 (x0 : type1605) := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) \/ (x0 y3 y4)) /\ (~ (x0 y1 (Nat.add y1 y2)))) y0).
Definition term473 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (x3 = x0) /\ ((x4 = x1) /\ (x2 x3 x4)).
Definition term406 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (x4 = x1) -> (x2 x0 x1) \/ (~ (x2 x3 x4)).
Definition term404 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := ((x2 x3 x4) = (x2 x0 x1)) -> (x2 x0 x1) \/ (~ (x2 x3 x4)).
Definition term388 (x0 : nat) (x1 : nat) := ((Nat.add x0 x1) = (Nat.add x0 x1)) -> Peano.le x0 (Nat.add x0 x1).
Definition term202 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (x0 = (Nat.add x1 x2)).
Definition term438 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term8 (x0 : type1605) := (((~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False) -> (~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False) -> ((~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False) -> (~ ((forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) = (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) -> False.
Definition term548 (x0 : type1605) (x1 : nat) := imp ((x0 x1 (Nat.add x1 (NUMERAL 0))) /\ (forall y0 : nat, (x0 x1 (Nat.add x1 y0)) -> x0 x1 (Nat.add x1 (S y0)))).
Definition term426 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term556 (x0 : type1605) (x1 : nat) := (fun y0 : nat => x0 y0 y0) x1.
Definition term391 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 (Nat.add x0 x1)).
Definition term419 (x0 : type1606) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x2))) -> x2 = (Nat.add x1 (x0 x1 x2)).
Definition term33 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ ((Peano.le x1 x2) -> x0 x1 x2).
Definition term262 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (exists y3 : nat, y2 = (Nat.add y1 y3))) y0.
Definition term257 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) y0.
Definition term284 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term89 (x0 : type1605) (x1 : nat) := (fun y0 : nat => exists y1 : nat, ~ (x0 y0 (Nat.add y0 y1))) x1.
Definition term537 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 x1 (Nat.add x1 y0)) (S x2).
Definition term524 (x0 : type1605) := imp (forall y0 : nat, forall y1 : nat, (x0 y0 (Nat.add y0 y1)) -> x0 y0 (S (Nat.add y0 y1))).
Definition term523 (x0 : type1605) := imp (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (x0 y0 y1)) -> x0 y0 (S y1)).
Definition term566 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 x1 (S (Nat.add x1 x2)).
Definition term536 (x0 : type1605) (x1 : nat) (x2 : nat) := imp (x0 x1 (Nat.add x1 x2)).
Definition term15 := fun y0 : type1605 => (~ ((forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2) = (forall y1 : nat, forall y2 : nat, y0 y1 (Nat.add y1 y2)))) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) = (exists y3 : nat, y2 = (Nat.add y1 y3))).
Definition term21 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term345 := fun y0 : type1606 => (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (forall y3 : nat, ~ (y2 = (Nat.add y1 y3)))) /\ ((fun y1 : type1606 => forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (y3 = (Nat.add y2 (y1 y2 y3)))) y0).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term444 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term410 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (~ (x3 = x0)) \/ ((~ (x4 = x1)) \/ ((x2 x0 x1) \/ (~ (x2 x3 x4)))).
Definition term470 (x0 : nat) (x1 : type1605) (x2 : nat) (x3 : nat) := (~ (~ (x3 = x0))) /\ (~ (~ (x1 x2 x3))).
Definition term37 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term267 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term415 (x0 : type1606) (x1 : nat) (x2 : nat) := (x2 = (Nat.add x1 (x0 x1 x2))) \/ (~ (Peano.le x1 x2)).
Definition term501 (x0 : type1605) := fun y0 : nat => fun y1 : nat => (x0 y0 y1) -> x0 y0 (S y1).
Definition term43 (x0 : type1605) (x1 : nat) := fun y0 : nat => (Peano.le x1 y0) /\ (~ (x0 x1 y0)).
Definition term494 (x0 : type1605) (x1 : nat) := forall y0 : nat, ((Peano.le x1 y0) /\ (x0 x1 y0)) -> x0 x1 (S y0).
Definition term146 (x0 : nat) (x1 : type1605) := fun y0 : nat => ((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2)).
Definition term198 (x0 : nat) (x1 : nat) := ~ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term521 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (x0 y0 (Nat.add y0 y1)) -> x0 y0 (S (Nat.add y0 y1)).
Definition term497 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> (x0 y0 y1) -> x0 y0 (S y1).
Definition term496 (x0 : type1605) := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (x0 y0 y1)) -> x0 y0 (S y1).
Definition term327 (x0 : type1606) := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (y1 = (Nat.add y0 (x0 y0 y1))).
Definition term217 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) \/ (forall y2 : nat, ~ (y1 = (Nat.add y0 y2)))) /\ ((~ (Peano.le y0 y1)) \/ (exists y2 : nat, y1 = (Nat.add y0 y2))).
Definition term142 (x0 : type1605) (x1 : nat) (x2 : nat) := and ((Peano.le x1 x2) /\ (~ (x0 x1 x2))).
Definition term153 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term349 (x0 : type1606) (x1 : nat) := fun y0 : nat => (~ (Peano.le x1 y0)) \/ (y0 = (Nat.add x1 (x0 x1 y0))).
Definition term368 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) \/ (~ (y1 = (Nat.add y0 y2))).
Definition term77 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1) /\ (~ (forall y0 : nat, forall y1 : nat, x0 y0 (Nat.add y0 y1))).
Definition term35 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x2)) \/ (x0 x1 x2).
Definition term107 (x0 : type1605) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) /\ (~ (x0 x1 (Nat.add x1 x2))).
Definition term397 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
Definition term100 (x0 : type1605) (x1 : nat) := exists y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ ((fun y1 : nat => ~ (x0 x1 (Nat.add x1 y1))) y0).
Definition term88 (x0 : type1605) := exists y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2)) /\ ((fun y1 : nat => exists y2 : nat, ~ (x0 y1 (Nat.add y1 y2))) y0).
Definition term487 (x0 : type1605) := forall y0 : nat, x0 y0 y0.
Definition term382 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x2 = (Nat.add x1 x0)))) -> Peano.le x1 x2.
Definition term560 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
Definition term183 (x0 : nat) (x1 : type1605) := @eq Prop ((exists y0 : nat, (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x1 y1 y2)) /\ (~ (x1 x0 (Nat.add x0 y0)))) \/ (exists y0 : nat, ((Peano.le x0 y0) /\ (~ (x1 x0 y0))) /\ (forall y1 : nat, forall y2 : nat, x1 y1 (Nat.add y1 y2)))).
Definition term182 (x0 : nat) (x1 : type1605) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x1 y2 y3)) /\ (~ (x1 x0 (Nat.add x0 y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => ((Peano.le x0 y1) /\ (~ (x1 x0 y1))) /\ (forall y2 : nat, forall y3 : nat, x1 y2 (Nat.add y2 y3))) y0)).
Definition term165 (x0 : type1605) := @eq Prop ((exists y0 : nat, exists y1 : nat, (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3)) /\ (~ (x0 y0 (Nat.add y0 y1)))) \/ (exists y0 : nat, exists y1 : nat, ((Peano.le y0 y1) /\ (~ (x0 y0 y1))) /\ (forall y2 : nat, forall y3 : nat, x0 y2 (Nat.add y2 y3)))).
Definition term164 (x0 : type1605) := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) \/ (x0 y3 y4)) /\ (~ (x0 y1 (Nat.add y1 y2)))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Peano.le y1 y2) /\ (~ (x0 y1 y2))) /\ (forall y3 : nat, forall y4 : nat, x0 y3 (Nat.add y3 y4))) y0)).
