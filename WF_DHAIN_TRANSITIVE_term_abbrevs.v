Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term83 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : Prop) := ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) = (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0))) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) = x2) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) = ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> x2).
Definition term110 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) (x3 : nat) := (fun y0 : nat => x0 (x1 y0) (x1 x2)) x3.
Definition term192 (x0 : nat -> Prop) := ~ (all x0).
Definition term319 := (~ False) -> False.
Definition term66 (a0 : Type') (x0 : type1402 a0) := forall y0 : nat -> a0, ((fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0) -> (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0.
Definition term44 (a0 : Type') (x0 : type1402 a0) := forall y0 : nat -> a0, ((fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0) -> (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0.
Definition term41 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0).
Definition term12 (x0 : type1605) := (forall y0 : type1605, ((forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) /\ (forall y1 : nat, y0 y1 (S y1))) -> forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> y0 y1 y2) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1.
Definition term323 (a0 : Type') (x0 : nat -> a0) (x1 : type1402 a0) := (fun y0 : type1402 a0 => (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 (x0 (S y1)) (x0 y1)) -> (~ ((forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 (x0 y2) (x0 y1)) /\ (y0 (x0 y3) (x0 y2))) -> y0 (x0 y3) (x0 y1)) /\ (forall y1 : nat, y0 (x0 (S y1)) (x0 y1)))) -> False) x1.
Definition term72 (a0 : Type') (x0 : type1402 a0) := (exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0) -> exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0.
Definition term56 (a0 : Type') (x0 : type1402 a0) := (exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0) -> exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0.
Definition term92 (x0 : nat) := Peano.lt x0 (S x0).
Definition term153 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False.
Definition term250 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := @eq Prop ((fun y0 : Prop => y0 = (exists y1 : nat, (exists y2 : nat, exists y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) /\ (~ (x0 (x1 y3) (x1 y1)))) \/ (~ (x0 (x1 (S y1)) (x1 y1))))) ((exists y0 : nat, exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) \/ (exists y0 : nat, ~ (x0 (x1 (S y0)) (x1 y0))))).
Definition term158 (x0 : Prop) := ~ (~ x0).
Definition term321 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (x0 (x1 (S x2)) (x1 x2)) -> False.
Definition term88 (a0 : Type') (x0 : type1402 a0) (x1 : nat) (x2 : nat -> a0) (x3 : nat) := (Peano.lt x3 x1) -> x0 (x2 x1) (x2 x3).
Definition term219 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := ~ (x0 (x1 (S x2)) (x1 x2)).
Definition term197 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) (x4 : nat) := ~ ((fun y0 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) -> x1 (x2 y0) (x2 x3)) x4).
Definition term326 (a0 : Type') := forall y0 : type1402 a0, (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (@WF a0 y0) = (~ (exists y1 : nat -> a0, forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> y0 (y1 y3) (y1 y2))).
Definition term154 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := ((forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False.
Definition term62 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := ((fun y0 : nat -> a0 => forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) x1) -> (fun y0 : nat -> a0 => forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) x1.
Definition term40 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := ((fun y0 : nat -> a0 => forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) x1) -> (fun y0 : nat -> a0 => forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) x1.
Definition term28 (a0 : Type') (x0 : type1402 a0) := @eq Prop (~ (exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1))).
Definition term265 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := or (exists y0 : nat, ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) /\ (~ (x1 (x2 y0) (x2 x3)))).
Definition term296 (a0 : Type') (x0 : type1402 a0) (x1 : nat) (x2 : nat -> a0) (x3 : nat) := (~ (x0 (x2 x1) (x2 x3))) -> x0 (x2 x1) (x2 x3).
Definition term273 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) /\ (~ (x1 (x2 y0) (x2 x3)))) x4.
Definition term100 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term278 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := @eq Prop ((exists y0 : nat, ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) /\ (~ (x1 (x2 y0) (x2 x3)))) \/ (~ (x1 (x2 (S x3)) (x2 x3)))).
Definition term277 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y1) (x2 x0))) /\ (~ (x1 (x2 y1) (x2 x3)))) y0) \/ (~ (x1 (x2 (S x3)) (x2 x3)))).
Definition term263 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := @eq Prop ((exists y0 : nat, exists y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2)))) \/ (~ (x0 (x1 (S x2)) (x1 x2)))).
Definition term262 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((x0 (x1 y1) (x1 x2)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 x2)))) y0) \/ (~ (x0 (x1 (S x2)) (x1 x2)))).
Definition term291 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => forall y1 : a0, ((~ (x0 x1 y0)) \/ (~ (x0 y0 y1))) \/ (x0 x1 y1)) x2.
Definition term227 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term94 (x0 : nat) := or (x0 = x0).
Definition term316 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat) (x3 : nat -> a0) (x4 : nat) := (x1 (x3 x0) (x3 x2)) /\ (x1 (x3 x2) (x3 x4)).
Definition term29 (a0 : Type') (x0 : type1402 a0) := ~ (exists y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)).
Definition term26 (a0 : Type') (x0 : type1402 a0) := ~ (exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1)).
Definition term65 (a0 : Type') (x0 : type1402 a0) := fun y0 : nat -> a0 => (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) -> forall y1 : nat, x0 (y0 (S y1)) (y0 y1).
Definition term43 (a0 : Type') (x0 : type1402 a0) := fun y0 : nat -> a0 => (forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) -> forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1).
Definition term199 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := fun y0 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) /\ (~ (x1 (x2 y0) (x2 x3))).
Definition term155 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (((forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False.
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term300 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := or (~ (x0 x1 x2)).
Definition term33 (a0 : Type') (x0 : type1402 a0) := fun y0 : nat -> a0 => forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1).
Definition term60 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := imp ((fun y0 : nat -> a0 => forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) x1).
Definition term36 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := imp ((fun y0 : nat -> a0 => forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) x1).
Definition term150 (x0 : Prop) := (~ x0) -> False.
Definition term252 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term314 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := imp (~ ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3)))).
Definition term298 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (x1 x0 x3)) \/ (x1 x2 x3).
Definition term32 (a0 : Type') (x0 : type1402 a0) := fun y0 : nat -> a0 => forall y1 : nat, x0 (y0 (S y1)) (y0 y1).
Definition term280 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat) (x3 : nat -> a0) (x4 : nat) := or (((x1 (x3 x0) (x3 x4)) /\ (x1 (x3 x2) (x3 x0))) /\ (~ (x1 (x3 x2) (x3 x4)))).
Definition term270 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := exists y0 : nat, (exists y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2)))) \/ (~ (x0 (x1 (S x2)) (x1 x2))).
Definition term248 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := exists y0 : nat, (exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) \/ (~ (x0 (x1 (S y0)) (x1 y0))).
Definition term258 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) (x3 : nat) := (fun y0 : nat => exists y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2)))) x3.
Definition term149 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0))) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0).
Definition term105 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y1) /\ ((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y1 y2)) -> (fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y2) /\ (forall y0 : nat, (fun y1 : nat => fun y2 : nat => x0 (x1 y2) (x1 y1)) y0 (S y0))) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (fun y2 : nat => fun y3 : nat => x0 (x1 y3) (x1 y2)) y0 y1.
Definition term9 (x0 : type1605) := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) /\ (forall y0 : nat, x0 y0 (S y0))) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1.
Definition term249 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (fun y0 : Prop => y0 = (exists y1 : nat, (exists y2 : nat, exists y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) /\ (~ (x0 (x1 y3) (x1 y1)))) \/ (~ (x0 (x1 (S y1)) (x1 y1))))) ((exists y0 : nat, exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) \/ (exists y0 : nat, ~ (x0 (x1 (S y0)) (x1 y0)))).
Definition term279 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) (x4 : nat) := or ((fun y0 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) /\ (~ (x1 (x2 y0) (x2 x3)))) x4).
Definition term113 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) (x4 : nat) := ((fun y0 : nat => fun y1 : nat => x1 (x2 y1) (x2 y0)) x0 x3) /\ ((fun y0 : nat => fun y1 : nat => x1 (x2 y1) (x2 y0)) x3 x4).
Definition term115 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) (x4 : nat) := imp (((fun y0 : nat => fun y1 : nat => x1 (x2 y1) (x2 y0)) x0 x3) /\ ((fun y0 : nat => fun y1 : nat => x1 (x2 y1) (x2 y0)) x3 x4)).
Definition term142 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) (x3 : nat) := (Peano.lt x2 x3) -> (fun y0 : nat => fun y1 : nat => x0 (x1 y1) (x1 y0)) x2 x3.
Definition term174 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := fun y0 : a0 => forall y1 : a0, ((x0 x1 y0) /\ (x0 y0 y1)) -> x0 x1 y1.
Definition term305 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term102 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) = True.
Definition term264 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) (x3 : nat) := or ((fun y0 : nat => exists y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2)))) x3).
Definition term215 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := ~ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)).
Definition term194 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := ~ (forall y0 : nat, ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) -> x1 (x2 y0) (x2 x3)).
Definition term112 (a0 : Type') (x0 : type1402 a0) (x1 : nat) (x2 : nat -> a0) (x3 : nat) := and (x0 (x2 x1) (x2 x3)).
Definition term208 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)).
Definition term201 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := ~ (forall y0 : nat, forall y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) -> x0 (x1 y1) (x1 x2)).
Definition term172 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := fun y0 : a0 => ((x1 x2 x0) /\ (x1 x0 y0)) -> x1 x2 y0.
Definition term254 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) \/ x1.
Definition term116 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat) (x3 : nat -> a0) (x4 : nat) := imp ((x1 (x3 x4) (x3 x0)) /\ (x1 (x3 x2) (x3 x4))).
Definition term320 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (~ (x0 (x1 (S x2)) (x1 x2))) -> x0 (x1 (S x2)) (x1 x2).
Definition term84 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : Prop) := ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) = x2) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) = ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> x2).
Definition term122 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := forall y0 : nat, ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) -> x1 (x2 y0) (x2 x3).
Definition term104 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> True.
Definition term163 (a0 : Type') (x0 : nat -> a0) := fun y0 : type1402 a0 => (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 (x0 (S y1)) (x0 y1)) -> (~ ((forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 (x0 y2) (x0 y1)) /\ (y0 (x0 y3) (x0 y2))) -> y0 (x0 y3) (x0 y1)) /\ (forall y1 : nat, y0 (x0 (S y1)) (x0 y1)))) -> False.
Definition term297 (x0 : Prop) := (~ x0) -> x0.
Definition term183 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (x1 x0 x2) /\ (x1 x2 x3).
Definition term108 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => x0 (x1 y0) (x1 x2).
Definition term301 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (x1 x0 x2)) \/ ((x1 x0 x3) \/ (~ (x1 x2 x3))).
Definition term63 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> forall y0 : nat, x0 (x1 (S y0)) (x1 y0).
Definition term164 (a0 : Type') (x0 : nat -> a0) := fun y0 : type1402 a0 => (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 (x0 (S y1)) (x0 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 (x0 y2) (x0 y1)) /\ (y0 (x0 y3) (x0 y2))) -> y0 (x0 y3) (x0 y1)) /\ (forall y1 : nat, y0 (x0 (S y1)) (x0 y1)).
Definition term267 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := (exists y0 : nat, ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) /\ (~ (x1 (x2 y0) (x2 x3)))) \/ (~ (x1 (x2 (S x3)) (x2 x3))).
Definition term242 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := or ((fun y0 : nat => exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) x2).
Definition term308 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term171 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((x1 x2 x0) /\ (x1 x0 x3)) -> x1 x2 x3.
Definition term86 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := forall y0 : nat, (Peano.lt x2 y0) -> x0 (x1 y0) (x1 x2).
Definition term286 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => exists y1 : nat, (((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2)))) \/ (~ (x0 (x1 (S x2)) (x1 x2))).
Definition term206 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => exists y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2))).
Definition term68 (a0 : Type') (x0 : type1402 a0) := imp (forall y0 : nat -> a0, ((fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0) -> (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0).
Definition term46 (a0 : Type') (x0 : type1402 a0) := imp (forall y0 : nat -> a0, ((fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0) -> (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0).
Definition term34 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (fun y0 : nat -> a0 => forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) x1.
Definition term196 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) -> x1 (x2 y0) (x2 x3)) x4.
Definition term223 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := or (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0))).
Definition term50 (a0 : Type') (x0 : type1402 a0) := exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1).
Definition term93 (x0 : nat) := (x0 = x0) \/ (Peano.lt x0 x0).
Definition term259 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((x0 (x1 y1) (x1 x2)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 x2)))) y0.
Definition term234 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) /\ (~ (x0 (x1 y3) (x1 y1)))) y0.
Definition term251 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := @eq Prop (((exists y0 : nat, exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) \/ (exists y0 : nat, ~ (x0 (x1 (S y0)) (x1 y0)))) = (exists y0 : nat, (exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) \/ (~ (x0 (x1 (S y0)) (x1 y0))))).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term302 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (x1 x0 x3) \/ ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3))).
Definition term221 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => ~ (x0 (x1 (S y0)) (x1 y0)).
Definition term188 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((~ (x0 y0 y1)) \/ (~ (x0 y1 y2))) \/ (x0 y0 y2).
Definition term176 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2.
Definition term269 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => (exists y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2)))) \/ (~ (x0 (x1 (S x2)) (x1 x2))).
Definition term247 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => (exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) \/ (~ (x0 (x1 (S y0)) (x1 y0))).
Definition term146 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> (fun y2 : nat => fun y3 : nat => x0 (x1 y3) (x1 y2)) y0 y1.
Definition term123 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => forall y1 : nat, (((fun y2 : nat => fun y3 : nat => x0 (x1 y3) (x1 y2)) x2 y0) /\ ((fun y2 : nat => fun y3 : nat => x0 (x1 y3) (x1 y2)) y0 y1)) -> (fun y2 : nat => fun y3 : nat => x0 (x1 y3) (x1 y2)) x2 y1.
Definition term237 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => ~ (x0 (x1 (S y0)) (x1 y0))) x2.
Definition term19 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term121 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := forall y0 : nat, (((fun y1 : nat => fun y2 : nat => x1 (x2 y2) (x2 y1)) x3 x0) /\ ((fun y1 : nat => fun y2 : nat => x1 (x2 y2) (x2 y1)) x0 y0)) -> (fun y1 : nat => fun y2 : nat => x1 (x2 y2) (x2 y1)) x3 y0.
Definition term239 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := exists y0 : nat, (fun y1 : nat => ~ (x0 (x1 (S y1)) (x1 y1))) y0.
Definition term64 (a0 : Type') (x0 : type1402 a0) := fun y0 : nat -> a0 => ((fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0) -> (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0.
Definition term42 (a0 : Type') (x0 : type1402 a0) := fun y0 : nat -> a0 => ((fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0) -> (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0.
Definition term75 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term318 (a0 : Type') (x0 : type1402 a0) (x1 : nat) (x2 : nat -> a0) (x3 : nat) := (x0 (x2 x1) (x2 x3)) -> False.
Definition term111 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) (x3 : nat) := and ((fun y0 : nat => fun y1 : nat => x0 (x1 y1) (x1 y0)) x2 x3).
Definition term324 (a0 : Type') (x0 : type1402 a0) := ((exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) -> exists y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) /\ ((exists y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) -> exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1)).
Definition term143 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => (Peano.lt x2 y0) -> (fun y1 : nat => fun y2 : nat => x0 (x1 y2) (x1 y1)) x2 y0.
Definition term322 (a0 : Type') (x0 : nat -> a0) := (fun y0 : nat -> a0 => forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 (y0 (S y2)) (y0 y2)) -> (~ ((forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 (y0 y3) (y0 y2)) /\ (y1 (y0 y4) (y0 y3))) -> y1 (y0 y4) (y0 y2)) /\ (forall y2 : nat, y1 (y0 (S y2)) (y0 y2)))) -> False) x0.
Definition term311 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := ~ (~ (x0 x1 x2)).
Definition term268 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, ((x0 (x1 y1) (x1 x2)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 x2)))) y0) \/ (~ (x0 (x1 (S x2)) (x1 x2))).
Definition term231 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) /\ (~ (x0 (x1 y3) (x1 y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => ~ (x0 (x1 (S y1)) (x1 y1))) y0).
Definition term266 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := ((fun y0 : nat => exists y1 : nat, ((x1 (x2 y0) (x2 x3)) /\ (x1 (x2 y1) (x2 y0))) /\ (~ (x1 (x2 y1) (x2 x3)))) x0) \/ (~ (x1 (x2 (S x3)) (x2 x3))).
Definition term274 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := fun y0 : nat => (fun y1 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y1) (x2 x0))) /\ (~ (x1 (x2 y1) (x2 x3)))) y0.
Definition term54 (a0 : Type') (x0 : type1402 a0) := exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0.
Definition term49 (a0 : Type') (x0 : type1402 a0) := exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0.
Definition term35 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := forall y0 : nat, x0 (x1 (S y0)) (x1 y0).
Definition term37 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := imp (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)).
Definition term96 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := x0 (x1 (S x2)) (x1 x2).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term184 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := fun y0 : a0 => ((~ (x1 x2 x0)) \/ (~ (x1 x0 y0))) \/ (x1 x2 y0).
Definition term140 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := imp ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0))).
Definition term139 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := imp ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y1) /\ ((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y1 y2)) -> (fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y2) /\ (forall y0 : nat, (fun y1 : nat => fun y2 : nat => x0 (x1 y2) (x1 y1)) y0 (S y0))).
Definition term203 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) -> x0 (x1 y1) (x1 x2)) x3.
Definition term73 (a0 : Type') (x0 : type1402 a0) := (exists y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) -> exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1).
Definition term57 (a0 : Type') (x0 : type1402 a0) := (exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) -> exists y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1).
Definition term307 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term226 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (exists y0 : nat, exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) \/ (exists y0 : nat, ~ (x0 (x1 (S y0)) (x1 y0))).
Definition term148 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (fun y2 : nat => fun y3 : nat => x0 (x1 y3) (x1 y2)) y0 y1.
Definition term130 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0).
Definition term129 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y1) /\ ((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y1 y2)) -> (fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y2.
Definition term126 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := forall y0 : nat, forall y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) -> x0 (x1 y1) (x1 x2).
Definition term125 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := forall y0 : nat, forall y1 : nat, (((fun y2 : nat => fun y3 : nat => x0 (x1 y3) (x1 y2)) x2 y0) /\ ((fun y2 : nat => fun y3 : nat => x0 (x1 y3) (x1 y2)) y0 y1)) -> (fun y2 : nat => fun y3 : nat => x0 (x1 y3) (x1 y2)) x2 y1.
Definition term39 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0).
Definition term14 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term11 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y0 y1.
Definition term90 (a0 : Type') (x0 : type1402 a0) (x1 : nat) (x2 : nat -> a0) (x3 : nat) := (Peano.lt x3 x1) -> (x0 (x2 x1) (x2 x3)) = True.
Definition term218 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := ~ ((fun y0 : nat => x0 (x1 (S y0)) (x1 y0)) x2).
Definition term85 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) x2.
Definition term288 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => exists y1 : nat, exists y2 : nat, (((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) \/ (~ (x0 (x1 (S y0)) (x1 y0))).
Definition term213 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0))).
Definition term81 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (x1 y2) (x1 y1)) = x2) -> (x2 -> (forall y1 : nat, x0 (x1 (S y1)) (x1 y1)) = y0) -> ((forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (x1 y2) (x1 y1)) -> forall y1 : nat, x0 (x1 (S y1)) (x1 y1)) = (x2 -> y0)) x3.
Definition term168 (a0 : Type') := fun y0 : nat -> a0 => forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 (y0 (S y2)) (y0 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 (y0 y3) (y0 y2)) /\ (y1 (y0 y4) (y0 y3))) -> y1 (y0 y4) (y0 y2)) /\ (forall y2 : nat, y1 (y0 (S y2)) (y0 y2)).
Definition term167 (a0 : Type') := fun y0 : nat -> a0 => forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 (y0 (S y2)) (y0 y2)) -> (~ ((forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 (y0 y3) (y0 y2)) /\ (y1 (y0 y4) (y0 y3))) -> y1 (y0 y4) (y0 y2)) /\ (forall y2 : nat, y1 (y0 (S y2)) (y0 y2)))) -> False.
Definition term232 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, exists y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) /\ (~ (x0 (x1 y3) (x1 y1)))) y0) \/ ((fun y1 : nat => ~ (x0 (x1 (S y1)) (x1 y1))) y0).
Definition term161 (a0 : Type') (x0 : type1402 a0) := imp (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2).
Definition term106 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => fun y1 : nat => x0 (x1 y1) (x1 y0).
Definition term271 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := (exists y0 : nat, (fun y1 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y1) (x2 x0))) /\ (~ (x1 (x2 y1) (x2 x3)))) y0) \/ (~ (x1 (x2 (S x3)) (x2 x3))).
Definition term18 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term99 := forall y0 : nat, True.
Definition term189 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, ((~ (x0 y0 y1)) \/ (~ (x0 y1 y2))) \/ (x0 y0 y2).
Definition term25 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2.
Definition term120 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := fun y0 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) -> x1 (x2 y0) (x2 x3).
Definition term295 (a0 : Type') (x0 : type1402 a0) (x1 : nat) (x2 : nat -> a0) (x3 : nat) := ~ (x0 (x2 x1) (x2 x3)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term253 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term159 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False.
Definition term70 (a0 : Type') (x0 : type1402 a0) := imp (exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0).
Definition term51 (a0 : Type') (x0 : type1402 a0) := imp (exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0).
Definition term98 := fun y0 : nat => True.
Definition term16 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term243 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := or (exists y0 : nat, exists y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2)))).
Definition term224 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := or (exists y0 : nat, exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))).
Definition term180 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := or ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3))).
Definition term256 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((x0 (x1 y1) (x1 x2)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 x2)))) y0) \/ (~ (x0 (x1 (S x2)) (x1 x2))).
Definition term210 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) x2.
Definition term299 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (x1 x0 x3) \/ (~ (x1 x2 x3)).
Definition term212 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) -> x0 (x1 y3) (x1 y1)) y0).
Definition term205 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, ((x0 (x1 y1) (x1 x2)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 x2)) y0).
Definition term246 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, exists y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) /\ (~ (x0 (x1 y3) (x1 y1)))) y0) \/ ((fun y1 : nat => ~ (x0 (x1 (S y1)) (x1 y1))) y0).
Definition term80 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : Prop) := forall y0 : Prop, ((forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (x1 y2) (x1 y1)) = x2) -> (x2 -> (forall y1 : nat, x0 (x1 (S y1)) (x1 y1)) = y0) -> ((forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (x1 y2) (x1 y1)) -> forall y1 : nat, x0 (x1 (S y1)) (x1 y1)) = (x2 -> y0).
Definition term76 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term114 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat) (x3 : nat -> a0) (x4 : nat) := (x1 (x3 x4) (x3 x0)) /\ (x1 (x3 x2) (x3 x4)).
Definition term222 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := exists y0 : nat, ~ (x0 (x1 (S y0)) (x1 y0)).
Definition term200 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := exists y0 : nat, ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) /\ (~ (x1 (x2 y0) (x2 x3))).
Definition term97 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => x0 (x1 (S y0)) (x1 y0).
Definition term144 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => (Peano.lt x2 y0) -> x0 (x1 y0) (x1 x2).
Definition term275 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := exists y0 : nat, (fun y1 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y1) (x2 x0))) /\ (~ (x1 (x2 y1) (x2 x3)))) y0.
Definition term141 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term317 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat) (x3 : nat -> a0) (x4 : nat) := ((x1 (x3 x2) (x3 x0)) /\ (x1 (x3 x0) (x3 x4))) -> x1 (x3 x2) (x3 x4).
Definition term118 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat) (x3 : nat -> a0) (x4 : nat) := ((x1 (x3 x0) (x3 x4)) /\ (x1 (x3 x2) (x3 x0))) -> x1 (x3 x2) (x3 x4).
Definition term78 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := forall y0 : Prop, forall y1 : Prop, ((forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (x1 y3) (x1 y2)) = y0) -> (y0 -> (forall y2 : nat, x0 (x1 (S y2)) (x1 y2)) = y1) -> ((forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (x1 y3) (x1 y2)) -> forall y2 : nat, x0 (x1 (S y2)) (x1 y2)) = (y0 -> y1).
Definition term77 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term152 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := ~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0))).
Definition term245 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (exists y0 : nat, exists y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2)))) \/ (~ (x0 (x1 (S x2)) (x1 x2))).
Definition term7 := forall y0 : type1605, ((forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) /\ (forall y1 : nat, y0 y1 (S y1))) -> forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> y0 y1 y2.
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term160 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term156 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (((forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False) -> ((forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False.
Definition term109 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) (x3 : nat) := (fun y0 : nat => fun y1 : nat => x0 (x1 y1) (x1 y0)) x2 x3.
Definition term69 (a0 : Type') (x0 : type1402 a0) := imp (forall y0 : nat -> a0, (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) -> forall y1 : nat, x0 (y0 (S y1)) (y0 y1)).
Definition term47 (a0 : Type') (x0 : type1402 a0) := imp (forall y0 : nat -> a0, (forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) -> forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)).
Definition term304 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := @eq Prop ((x1 x0 x3) \/ ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3)))).
Definition term185 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := forall y0 : a0, ((~ (x1 x2 x0)) \/ (~ (x1 x0 y0))) \/ (x1 x2 y0).
Definition term103 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) = True) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) = ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> True).
Definition term132 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)).
Definition term131 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y1) /\ ((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y1 y2)) -> (fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y2).
Definition term170 (a0 : Type') := forall y0 : nat -> a0, forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 (y0 (S y2)) (y0 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 (y0 y3) (y0 y2)) /\ (y1 (y0 y4) (y0 y3))) -> y1 (y0 y4) (y0 y2)) /\ (forall y2 : nat, y1 (y0 (S y2)) (y0 y2)).
Definition term169 (a0 : Type') := forall y0 : nat -> a0, forall y1 : type1402 a0, (forall y2 : a0, forall y3 : a0, forall y4 : a0, ((y1 y2 y3) /\ (y1 y3 y4)) -> y1 y2 y4) -> (forall y2 : nat, y1 (y0 (S y2)) (y0 y2)) -> (~ ((forall y2 : nat, forall y3 : nat, forall y4 : nat, ((y1 (y0 y3) (y0 y2)) /\ (y1 (y0 y4) (y0 y3))) -> y1 (y0 y4) (y0 y2)) /\ (forall y2 : nat, y1 (y0 (S y2)) (y0 y2)))) -> False.
Definition term173 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) := forall y0 : a0, ((x1 x2 x0) /\ (x1 x0 y0)) -> x1 x2 y0.
Definition term233 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) x2.
Definition term8 (x0 : type1605) := (fun y0 : type1605 => ((forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) /\ (forall y1 : nat, y0 y1 (S y1))) -> forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> y0 y1 y2) x0.
Definition term217 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => x0 (x1 (S y0)) (x1 y0)) x2.
Definition term292 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (fun y0 : a0 => ((~ (x1 x2 x0)) \/ (~ (x1 x0 y0))) \/ (x1 x2 y0)) x3.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term53 (a0 : Type') (x0 : type1402 a0) := fun y0 : nat -> a0 => (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0.
Definition term48 (a0 : Type') (x0 : type1402 a0) := fun y0 : nat -> a0 => (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0.
Definition term190 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat) (x3 : nat -> a0) (x4 : nat) := ~ (((x1 (x3 x0) (x3 x4)) /\ (x1 (x3 x2) (x3 x0))) -> x1 (x3 x2) (x3 x4)).
Definition term191 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat) (x3 : nat -> a0) (x4 : nat) := ((x1 (x3 x0) (x3 x4)) /\ (x1 (x3 x2) (x3 x0))) /\ (~ (x1 (x3 x2) (x3 x4))).
Definition term166 (a0 : Type') (x0 : nat -> a0) := forall y0 : type1402 a0, (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 (x0 (S y1)) (x0 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 (x0 y2) (x0 y1)) /\ (y0 (x0 y3) (x0 y2))) -> y0 (x0 y3) (x0 y1)) /\ (forall y1 : nat, y0 (x0 (S y1)) (x0 y1)).
Definition term135 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => x0 (x1 y2) (x1 y1)) y0 (S y0).
Definition term165 (a0 : Type') (x0 : nat -> a0) := forall y0 : type1402 a0, (forall y1 : a0, forall y2 : a0, forall y3 : a0, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) -> (forall y1 : nat, y0 (x0 (S y1)) (x0 y1)) -> (~ ((forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 (x0 y2) (x0 y1)) /\ (y0 (x0 y3) (x0 y2))) -> y0 (x0 y3) (x0 y1)) /\ (forall y1 : nat, y0 (x0 (S y1)) (x0 y1)))) -> False.
Definition term244 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := ((fun y0 : nat => exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) x2) \/ ((fun y0 : nat => ~ (x0 (x1 (S y0)) (x1 y0))) x2).
Definition term55 (a0 : Type') (x0 : type1402 a0) := exists y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1).
Definition term187 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := forall y0 : a0, forall y1 : a0, ((~ (x0 x1 y0)) \/ (~ (x0 y0 y1))) \/ (x0 x1 y1).
Definition term175 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := forall y0 : a0, forall y1 : a0, ((x0 x1 y0) /\ (x0 y0 y1)) -> x0 x1 y1.
Definition term325 (a0 : Type') (x0 : type1402 a0) := (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (@WF a0 x0) = (~ (exists y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term272 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := exists y0 : nat, ((fun y1 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y1) (x2 x0))) /\ (~ (x1 (x2 y1) (x2 x3)))) y0) \/ (~ (x1 (x2 (S x3)) (x2 x3))).
Definition term257 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, ((x0 (x1 y1) (x1 x2)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 x2)))) y0) \/ (~ (x0 (x1 (S x2)) (x1 x2))).
Definition term282 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : type1402 a0) (x3 : nat -> a0) (x4 : nat) := (((x2 (x3 x0) (x3 x4)) /\ (x2 (x3 x1) (x3 x0))) /\ (~ (x2 (x3 x1) (x3 x4)))) \/ (~ (x2 (x3 (S x4)) (x3 x4))).
Definition term309 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ~ ((~ (x1 x0 x2)) \/ (~ (x1 x2 x3))).
Definition term182 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ((~ (x1 x2 x0)) \/ (~ (x1 x0 x3))) \/ (x1 x2 x3).
Definition term216 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := exists y0 : nat, ~ ((fun y1 : nat => x0 (x1 (S y1)) (x1 y1)) y0).
Definition term209 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) -> x0 (x1 y3) (x1 y1)) y0).
Definition term202 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, ((x0 (x1 y1) (x1 x2)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 x2)) y0).
Definition term195 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := exists y0 : nat, ~ ((fun y1 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y1) (x2 x0))) -> x1 (x2 y1) (x2 x3)) y0).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0) -> (forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term119 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := fun y0 : nat => (((fun y1 : nat => fun y2 : nat => x1 (x2 y2) (x2 y1)) x3 x0) /\ ((fun y1 : nat => fun y2 : nat => x1 (x2 y2) (x2 y1)) x0 y0)) -> (fun y1 : nat => fun y2 : nat => x1 (x2 y2) (x2 y1)) x3 y0.
Definition term293 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (x1 x2 x0)) \/ ((~ (x1 x0 x3)) \/ (x1 x2 x3)).
Definition term225 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0))) \/ (~ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0))).
Definition term27 (a0 : Type') (x0 : type1402 a0) := @eq Prop (@WF a0 x0).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term238 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => (fun y1 : nat => ~ (x0 (x1 (S y1)) (x1 y1))) y0.
Definition term107 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => fun y1 : nat => x0 (x1 y1) (x1 y0)) x2.
Definition term290 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((~ (x0 y0 y1)) \/ (~ (x0 y1 y2))) \/ (x0 y0 y2)) x1.
Definition term315 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := imp ((x1 x0 x2) /\ (x1 x2 x3)).
Definition term294 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := ~ (x0 x1 x2).
Definition term157 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := ~ (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))).
Definition term101 (x0 : Prop) := forall y0 : nat, x0.
Definition term89 (a0 : Type') (x0 : type1402 a0) (x1 : nat) (x2 : nat -> a0) (x3 : nat) := x0 (x2 x1) (x2 x3).
Definition term67 (a0 : Type') (x0 : type1402 a0) := forall y0 : nat -> a0, (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) -> forall y1 : nat, x0 (y0 (S y1)) (y0 y1).
Definition term45 (a0 : Type') (x0 : type1402 a0) := forall y0 : nat -> a0, (forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) -> forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1).
Definition term260 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((x0 (x1 y1) (x1 x2)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 x2)))) y0.
Definition term235 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) /\ (~ (x0 (x1 y3) (x1 y1)))) y0.
Definition term289 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := exists y0 : nat, exists y1 : nat, exists y2 : nat, (((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) \/ (~ (x0 (x1 (S y0)) (x1 y0))).
Definition term287 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := exists y0 : nat, exists y1 : nat, (((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2)))) \/ (~ (x0 (x1 (S x2)) (x1 x2))).
Definition term214 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := exists y0 : nat, exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0))).
Definition term207 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := exists y0 : nat, exists y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) /\ (~ (x0 (x1 y1) (x1 x2))).
Definition term181 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ ((x1 x2 x0) /\ (x1 x0 x3))) \/ (x1 x2 x3).
Definition term91 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (Peano.lt x2 (S x2)) -> (x0 (x1 (S x2)) (x1 x2)) = True.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x1 y0.
Definition term230 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term177 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := ~ ((x1 x0 x2) /\ (x1 x2 x3)).
Definition term220 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => ~ ((fun y1 : nat => x0 (x1 (S y1)) (x1 y1)) y0).
Definition term198 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := fun y0 : nat => ~ ((fun y1 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y1) (x2 x0))) -> x1 (x2 y1) (x2 x3)) y0).
Definition term162 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)).
Definition term145 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := forall y0 : nat, (Peano.lt x2 y0) -> (fun y1 : nat => fun y2 : nat => x0 (x1 y2) (x1 y1)) x2 y0.
Definition term186 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := fun y0 : a0 => forall y1 : a0, ((~ (x0 x1 y0)) \/ (~ (x0 y0 y1))) \/ (x0 x1 y1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term283 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := fun y0 : nat => ((fun y1 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y1) (x2 x0))) /\ (~ (x1 (x2 y1) (x2 x3)))) y0) \/ (~ (x1 (x2 (S x3)) (x2 x3))).
Definition term13 := (forall y0 : type1605, ((forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) /\ (forall y1 : nat, y0 y1 (S y1))) -> forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> y0 y1 y2) -> forall y0 : type1605, ((forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 y1 y2) /\ (y0 y2 y3)) -> y0 y1 y3) /\ (forall y1 : nat, y0 y1 (S y1))) -> forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> y0 y1 y2.
Definition term134 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => x0 (x1 y0) (x1 x2)) (S x2).
Definition term204 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) (x3 : nat) := ~ ((fun y0 : nat => forall y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) -> x0 (x1 y1) (x1 x2)) x3).
Definition term151 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (~ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)))) -> False.
Definition term276 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := or (exists y0 : nat, (fun y1 : nat => ((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y1) (x2 x0))) /\ (~ (x1 (x2 y1) (x2 x3)))) y0).
Definition term261 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((x0 (x1 y1) (x1 x2)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 x2)))) y0).
Definition term236 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) /\ (~ (x0 (x1 y3) (x1 y1)))) y0).
Definition term285 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := exists y0 : nat, (((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) /\ (~ (x1 (x2 y0) (x2 x3)))) \/ (~ (x1 (x2 (S x3)) (x2 x3))).
Definition term136 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => x0 (x1 y2) (x1 y1)) y0 (S y0).
Definition term284 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) := fun y0 : nat => (((x1 (x2 x0) (x2 x3)) /\ (x1 (x2 y0) (x2 x0))) /\ (~ (x1 (x2 y0) (x2 x3)))) \/ (~ (x1 (x2 (S x3)) (x2 x3))).
Definition term211 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := ~ ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) x2).
Definition term133 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => fun y1 : nat => x0 (x1 y1) (x1 y0)) x2 (S x2).
Definition term95 (x0 : nat) := True \/ (Peano.lt x0 x0).
Definition term313 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := and (x0 x1 x2).
Definition term71 (a0 : Type') (x0 : type1402 a0) := imp (exists y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)).
Definition term52 (a0 : Type') (x0 : type1402 a0) := imp (exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1)).
Definition term303 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := @eq Prop ((~ (x1 x2 x0)) \/ ((~ (x1 x0 x3)) \/ (x1 x2 x3))).
Definition term61 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := imp (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)).
Definition term79 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (x1 y3) (x1 y2)) = y0) -> (y0 -> (forall y2 : nat, x0 (x1 (S y2)) (x1 y2)) = y1) -> ((forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (x1 y3) (x1 y2)) -> forall y2 : nat, x0 (x1 (S y2)) (x1 y2)) = (y0 -> y1)) x2.
Definition term228 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term310 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (~ (x1 x0 x2))) /\ (~ (~ (x1 x2 x3))).
Definition term138 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0)) /\ (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)).
Definition term137 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y1) /\ ((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y1 y2)) -> (fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y2) /\ (forall y0 : nat, (fun y1 : nat => fun y2 : nat => x0 (x1 y2) (x1 y1)) y0 (S y0)).
Definition term10 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) /\ (forall y0 : nat, x0 y0 (S y0)).
Definition term74 (a0 : Type') (x0 : type1402 a0) := (forall y0 : nat -> a0, (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) -> forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) -> (exists y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) -> exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1).
Definition term59 (a0 : Type') (x0 : type1402 a0) := (forall y0 : nat -> a0, ((fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0) -> (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0) -> (exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0) -> exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0.
Definition term58 (a0 : Type') (x0 : type1402 a0) := (forall y0 : nat -> a0, (forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) -> forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) -> (exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1)) -> exists y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1).
Definition term31 (a0 : Type') (x0 : type1402 a0) := (forall y0 : nat -> a0, ((fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0) -> (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0) -> (exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, x0 (y1 (S y2)) (y1 y2)) y0) -> exists y0 : nat -> a0, (fun y1 : nat -> a0 => forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> x0 (y1 y3) (y1 y2)) y0.
Definition term30 (a0 : Type') (x0 : type976 a0) (x1 : type976 a0) := (forall y0 : nat -> a0, (x0 y0) -> x1 y0) -> (exists y0 : nat -> a0, x0 y0) -> exists y0 : nat -> a0, x1 y0.
Definition term281 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : type1402 a0) (x3 : nat -> a0) (x4 : nat) := ((fun y0 : nat => ((x2 (x3 x0) (x3 x4)) /\ (x2 (x3 y0) (x3 x0))) /\ (~ (x2 (x3 y0) (x3 x4)))) x1) \/ (~ (x2 (x3 (S x4)) (x3 x4))).
Definition term193 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term178 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ (x1 x0 x2)) \/ (~ (x1 x2 x3)).
Definition term117 (a0 : Type') (x0 : nat) (x1 : type1402 a0) (x2 : nat -> a0) (x3 : nat) (x4 : nat) := (((fun y0 : nat => fun y1 : nat => x1 (x2 y1) (x2 y0)) x3 x0) /\ ((fun y0 : nat => fun y1 : nat => x1 (x2 y1) (x2 y0)) x0 x4)) -> (fun y0 : nat => fun y1 : nat => x1 (x2 y1) (x2 y0)) x3 x4.
Definition term312 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := and (~ (~ (x0 x1 x2))).
Definition term147 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0).
Definition term124 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => forall y1 : nat, ((x0 (x1 y0) (x1 x2)) /\ (x0 (x1 y1) (x1 y0))) -> x0 (x1 y1) (x1 x2).
Definition term179 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := or (~ ((x1 x0 x2) /\ (x1 x2 x3))).
Definition term229 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term255 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) \/ x1.
Definition term128 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) -> x0 (x1 y2) (x1 y0).
Definition term127 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := fun y0 : nat => forall y1 : nat, forall y2 : nat, (((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y1) /\ ((fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y1 y2)) -> (fun y3 : nat => fun y4 : nat => x0 (x1 y4) (x1 y3)) y0 y2.
Definition term82 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : Prop) (x3 : Prop) := ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) = x2) -> (x2 -> (forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) = x3) -> ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 (x1 y1) (x1 y0)) -> forall y0 : nat, x0 (x1 (S y0)) (x1 y0)) = (x2 -> x3).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term38 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := (fun y0 : nat -> a0 => forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 (y0 y2) (y0 y1)) x1.
Definition term87 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Peano.lt x2 y0) -> x0 (x1 y0) (x1 x2)) x3.
Definition term306 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : a0) (x3 : a0) := (~ ((~ (x1 x2 x0)) \/ (~ (x1 x0 x3)))) -> x1 x2 x3.
Definition term241 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := @eq Prop ((exists y0 : nat, exists y1 : nat, exists y2 : nat, ((x0 (x1 y1) (x1 y0)) /\ (x0 (x1 y2) (x1 y1))) /\ (~ (x0 (x1 y2) (x1 y0)))) \/ (exists y0 : nat, ~ (x0 (x1 (S y0)) (x1 y0)))).
Definition term240 (a0 : Type') (x0 : type1402 a0) (x1 : nat -> a0) := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((x0 (x1 y2) (x1 y1)) /\ (x0 (x1 y3) (x1 y2))) /\ (~ (x0 (x1 y3) (x1 y1)))) y0) \/ (exists y0 : nat, (fun y1 : nat => ~ (x0 (x1 (S y1)) (x1 y1))) y0)).
