Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term266 := fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (real_lt y1 y2)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) \/ (real_lt (real_pow y1 y0) (real_pow y2 y0)).
Definition term253 := fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) \/ (real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term49 := fun y0 : nat => forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2).
Definition term37 := fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term31 := fun y0 : nat => forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0).
Definition term73 (x0 : nat -> Prop) := ~ (all x0).
Definition term57 (x0 : real -> Prop) := ~ (all x0).
Definition term33 (x0 : real) (x1 : nat) := fun y0 : real => ((real_le x0 y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_le (real_pow x0 x1) (real_pow y0 x1).
Definition term311 := (~ False) -> False.
Definition term21 := imp (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)).
Definition term61 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow x1 x0) (real_pow y0 x0)) = (real_lt x1 y0)) x2.
Definition term271 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (real_lt y1 y2)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) \/ (real_lt (real_pow y1 y0) (real_pow y2 y0))) x0.
Definition term268 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) \/ (real_le (real_pow y1 y0) (real_pow y2 y0))) x0.
Definition term76 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2)) x0.
Definition term158 (x0 : nat) := (exists y0 : real, exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y0 : real, exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1)).
Definition term115 (x0 : nat) (x1 : real) := fun y0 : real => (fun y1 : real => (real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) y0.
Definition term293 (x0 : nat) (x1 : real) (x2 : real) := (~ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (real_le (real_pow x1 x0) (real_pow x2 x0)))) -> ~ (real_le x1 x2).
Definition term284 (x0 : Prop) := ~ (~ x0).
Definition term298 (x0 : real) (x1 : real) (x2 : nat) := (~ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))) /\ (~ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term25 := (~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)).
Definition term270 (x0 : real) (x1 : nat) (x2 : real) := (fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x1))) \/ (real_le (real_pow x0 x1) (real_pow y0 x1))) x2.
Definition term236 := and (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))).
Definition term300 (x0 : nat) := and (~ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))).
Definition term84 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term214 (x0 : real) := and (forall y0 : real, (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))).
Definition term182 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term319 (x0 : nat) (x1 : real) (x2 : real) := @eq Prop ((real_lt (real_pow x1 x0) (real_pow x2 x0)) \/ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (~ (real_lt x1 x2)))).
Definition term226 (x0 : real) := and ((fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) x0).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term23 := (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)).
Definition term217 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_lt y0 x0).
Definition term171 (x0 : nat) (x1 : real) := (fun y0 : real => exists y1 : real, ((real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))) x1.
Definition term145 (x0 : nat) (x1 : real) := (fun y0 : real => exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1)) x1.
Definition term143 (x0 : nat) (x1 : real) := (fun y0 : real => exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) x1.
Definition term170 (x0 : nat) := exists y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y1 : real => exists y2 : real, ((real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ ((~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0).
Definition term127 (x0 : nat) := exists y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y1 : real => (exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ (exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0).
Definition term85 (x0 : nat) (x1 : real) := exists y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y1 : real => ((real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1))) y0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term120 (x0 : nat) (x1 : real) := fun y0 : real => (fun y1 : real => (~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1)) y0.
Definition term281 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_lt (real_pow x0 x2) (real_pow x1 x2))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term235 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0).
Definition term213 (x0 : real) := and (forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0).
Definition term56 (x0 : nat) (x1 : real) (x2 : real) := ~ ((Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow x1 x0) (real_pow x2 x0)) = (real_lt x1 x2)).
Definition term81 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term178 (x0 : nat) := fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y1 : real, ((real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term313 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_lt x0 x1)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term260 (x0 : real) (x1 : real) (x2 : nat) := ((~ (real_lt x0 x1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term59 (x0 : nat) (x1 : real) := ~ (forall y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow x1 x0) (real_pow y0 x0)) = (real_lt x1 y0)).
Definition term27 (x0 : real) (x1 : nat) := fun y0 : real => ((real_lt x0 y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_lt (real_pow x0 x1) (real_pow y0 x1).
Definition term219 := fun y0 : real => (forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)).
Definition term189 (x0 : real) (x1 : real) := ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))) /\ ((real_le x1 x0) \/ (real_lt x0 x1)).
Definition term55 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (((real_lt (real_pow x1 x0) (real_pow x2 x0)) /\ (~ (real_lt x1 x2))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow x2 x0))) /\ (real_lt x1 x2))).
Definition term201 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_lt y0 x0).
Definition term288 (x0 : real) (x1 : real) := (real_lt x1 x0) -> ~ (real_le x0 x1).
Definition term240 := (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)).
Definition term309 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) -> real_lt x0 x1.
Definition term135 (x0 : nat) := fun y0 : real => (fun y1 : real => (exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ (exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0.
Definition term310 (x0 : real) (x1 : real) := (real_lt x0 x1) -> False.
Definition term44 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow x1 x0) (real_pow x2 x0)) = (real_lt x1 x2).
Definition term282 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term222 := (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0).
Definition term199 (x0 : real) := (forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ (forall y0 : real, (fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0).
Definition term312 (x0 : real) (x1 : real) (x2 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ ((~ (real_lt x0 x1)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term188 (x0 : real) (x1 : real) := ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))) /\ ((~ (~ (real_le x1 x0))) \/ (real_lt x0 x1)).
Definition term169 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y0 : real, (fun y1 : real => exists y2 : real, ((real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ ((~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0).
Definition term128 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y0 : real, (fun y1 : real => (exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ (exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0).
Definition term86 (x0 : nat) (x1 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y0 : real, (fun y1 : real => ((real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1))) y0).
Definition term146 (x0 : nat) (x1 : real) := ((fun y0 : real => exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) x1) \/ ((fun y0 : real => exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1)) x1).
Definition term88 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => ((real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0))) x2.
Definition term168 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y0 : real, exists y1 : real, ((real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term16 := ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)).
Definition term10 := ~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2)).
Definition term82 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term138 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y0 : real, (exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term96 (x0 : nat) (x1 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y0 : real, ((real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0))).
Definition term106 (x0 : nat) (x1 : real) (x2 : real) := (real_lt (real_pow x1 x0) (real_pow x2 x0)) /\ (~ (real_lt x1 x2)).
Definition term307 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_lt x0 x1)).
Definition term315 (x0 : nat) := or (~ (Coq.Arith.PeanoNat.Nat.Odd x0)).
Definition term273 (x0 : real) (x1 : nat) (x2 : real) := (fun y0 : real => ((~ (real_lt x0 y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x1))) \/ (real_lt (real_pow x0 x1) (real_pow y0 x1))) x2.
Definition term280 (x0 : Prop) := (~ x0) -> x0.
Definition term301 (x0 : real) (x1 : real) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x2) /\ (~ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term248 (x0 : real) (x1 : real) (x2 : nat) := (real_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2).
Definition term237 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0.
Definition term232 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0.
Definition term105 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => (real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) x2.
Definition term296 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term257 (x0 : real) (x1 : real) (x2 : nat) := or (~ ((real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2))).
Definition term244 (x0 : real) (x1 : real) (x2 : nat) := or (~ ((real_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2))).
Definition term136 (x0 : nat) := exists y0 : real, (fun y1 : real => (exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ (exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0.
Definition term121 (x0 : nat) (x1 : real) := exists y0 : real, (fun y1 : real => (~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1)) y0.
Definition term116 (x0 : nat) (x1 : real) := exists y0 : real, (fun y1 : real => (real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) y0.
Definition term94 (x0 : nat) (x1 : real) := exists y0 : real, (fun y1 : real => ((real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1))) y0.
Definition term22 := (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term265 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (real_lt y0 y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))) \/ (real_lt (real_pow y0 x0) (real_pow y1 x0)).
Definition term252 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))) \/ (real_le (real_pow y0 x0) (real_pow y1 x0)).
Definition term239 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0).
Definition term234 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0)).
Definition term193 := forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ ((real_le y0 y1) \/ (real_lt y1 y0)).
Definition term48 (x0 : nat) := forall y0 : real, forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow y0 x0) (real_pow y1 x0)) = (real_lt y0 y1).
Definition term43 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0).
Definition term36 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term30 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_lt y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term191 (x0 : real) := forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ ((real_le x0 y0) \/ (real_lt y0 x0)).
Definition term107 (x0 : nat) (x1 : real) (x2 : real) := or ((fun y0 : real => (real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) x2).
Definition term167 (x0 : nat) := exists y0 : real, exists y1 : real, ((real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1)).
Definition term157 (x0 : nat) := exists y0 : real, exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1).
Definition term152 (x0 : nat) := exists y0 : real, exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1)).
Definition term72 (x0 : nat) := exists y0 : real, exists y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (((real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term195 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term19 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term83 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term153 (x0 : nat) := or (exists y0 : real, (fun y1 : real => exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) y0).
Definition term118 (x0 : nat) (x1 : real) := or (exists y0 : real, (fun y1 : real => (real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) y0).
Definition term328 (x0 : real) (x1 : real) (x2 : nat) := imp (~ ((~ (real_lt x0 x1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2)))).
Definition term95 (x0 : nat) (x1 : real) := exists y0 : real, ((real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0)).
Definition term185 (x0 : real) (x1 : real) := (~ (~ (real_le x1 x0))) \/ (real_lt x0 x1).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term34 (x0 : real) (x1 : nat) := forall y0 : real, ((real_le x0 y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_le (real_pow x0 x1) (real_pow y0 x1).
Definition term28 (x0 : real) (x1 : nat) := forall y0 : real, ((real_lt x0 y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_lt (real_pow x0 x1) (real_pow y0 x1).
Definition term67 (x0 : nat) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow y1 x0) (real_pow y2 x0)) = (real_lt y1 y2)) y0).
Definition term60 (x0 : nat) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow x1 x0) (real_pow y1 x0)) = (real_lt x1 y1)) y0).
Definition term190 (x0 : real) := fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ ((real_le x0 y0) \/ (real_lt y0 x0)).
Definition term93 (x0 : nat) (x1 : real) := fun y0 : real => (fun y1 : real => ((real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1))) y0.
Definition term104 (x0 : nat) (x1 : real) := fun y0 : real => (~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0).
Definition term243 (x0 : real) (x1 : real) (x2 : nat) := real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term327 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term303 (x0 : real) (x1 : real) (x2 : nat) := imp ((Coq.Arith.PeanoNat.Nat.Odd x2) /\ (~ (real_le (real_pow x0 x2) (real_pow x1 x2)))).
Definition term79 := fun y0 : nat => exists y1 : real, exists y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) /\ (((real_lt (real_pow y1 y0) (real_pow y2 y0)) /\ (~ (real_lt y1 y2))) \/ ((~ (real_lt (real_pow y1 y0) (real_pow y2 y0))) /\ (real_lt y1 y2))).
Definition term40 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) = (real_lt y0 x0).
Definition term70 (x0 : nat) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow y1 x0) (real_pow y2 x0)) = (real_lt y1 y2)) y0).
Definition term231 := @eq Prop (forall y0 : real, (forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0))).
Definition term230 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0)).
Definition term209 (x0 : real) := @eq Prop (forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ ((real_le x0 y0) \/ (real_lt y0 x0))).
Definition term208 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ ((fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0)).
Definition term302 (x0 : real) (x1 : real) (x2 : nat) := imp (~ ((~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)))).
Definition term141 (x0 : nat) := fun y0 : real => exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1)).
Definition term290 (x0 : real) (x1 : real) (x2 : nat) := ~ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term264 (x0 : nat) := fun y0 : real => forall y1 : real, ((~ (real_lt y0 y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))) \/ (real_lt (real_pow y0 x0) (real_pow y1 x0)).
Definition term251 (x0 : nat) := fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))) \/ (real_le (real_pow y0 x0) (real_pow y1 x0)).
Definition term192 := fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ ((real_le y0 y1) \/ (real_lt y1 y0)).
Definition term47 (x0 : nat) := fun y0 : real => forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow y0 x0) (real_pow y1 x0)) = (real_lt y0 y1).
Definition term35 (x0 : nat) := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term29 (x0 : nat) := fun y0 : real => forall y1 : real, ((real_lt y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term308 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_lt x0 x1.
Definition term330 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_pow x0 x2) (real_pow x1 x2)) -> False.
Definition term15 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term186 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_lt x0 x1).
Definition term130 (x0 : nat) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))) x1.
Definition term278 (x0 : real) (x1 : real) (x2 : nat) := ~ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term87 (x0 : nat) (x1 : real) := fun y0 : real => ((real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0)).
Definition term329 (x0 : real) (x1 : real) (x2 : nat) := imp ((real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term41 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) = (real_lt y0 x0).
Definition term14 := (((~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False) -> ((~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term99 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term123 (x0 : nat) (x1 : real) := (exists y0 : real, (real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ (exists y0 : real, (~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0)).
Definition term279 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> Coq.Arith.PeanoNat.Nat.Odd x0.
Definition term299 (x0 : nat) := ~ (~ (Coq.Arith.PeanoNat.Nat.Odd x0)).
Definition term66 (x0 : nat) := ~ (forall y0 : real, forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow y0 x0) (real_pow y1 x0)) = (real_lt y0 y1)).
Definition term12 := ((~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term110 (x0 : nat) (x1 : real) (x2 : real) := (~ (real_lt (real_pow x1 x0) (real_pow x2 x0))) /\ (real_lt x1 x2).
Definition term276 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term184 (x0 : real) (x1 : real) := or (real_le x0 x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term294 (x0 : real) (x1 : real) (x2 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term117 (x0 : nat) (x1 : real) := exists y0 : real, (real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0)).
Definition term305 (x0 : real) (x1 : real) := (real_le x0 x1) -> ~ (real_le x0 x1).
Definition term172 (x0 : nat) := fun y0 : real => (fun y1 : real => exists y2 : real, ((real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ ((~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0.
Definition term155 (x0 : nat) := fun y0 : real => (fun y1 : real => exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2)) y0.
Definition term150 (x0 : nat) := fun y0 : real => (fun y1 : real => exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) y0.
Definition term324 (x0 : real) (x1 : real) (x2 : nat) := ~ ((~ (real_lt x0 x1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))).
Definition term100 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term261 (x0 : real) (x1 : real) (x2 : nat) := (real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2).
Definition term295 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term262 (x0 : real) (x1 : nat) := fun y0 : real => ((~ (real_lt x0 y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x1))) \/ (real_lt (real_pow x0 x1) (real_pow y0 x1)).
Definition term218 (x0 : real) := (forall y0 : real, (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) /\ (forall y0 : real, (real_le x0 y0) \/ (real_lt y0 x0)).
Definition term267 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (real_lt y1 y2)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) \/ (real_lt (real_pow y1 y0) (real_pow y2 y0)).
Definition term254 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) \/ (real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term38 := forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term17 := forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0).
Definition term8 := forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2).
Definition term179 (x0 : nat) := exists y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y1 : real, ((real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term166 (x0 : nat) := fun y0 : real => exists y1 : real, ((real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1)).
Definition term71 (x0 : nat) := fun y0 : real => exists y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (((real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term13 := (((~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term318 (x0 : real) (x1 : real) (x2 : nat) := @eq Prop ((~ (real_lt x0 x1)) \/ ((~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)))).
Definition term212 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0)).
Definition term320 (x0 : nat) (x1 : real) (x2 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (~ (real_lt x1 x2)).
Definition term187 (x0 : real) (x1 : real) := and ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))).
Definition term210 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0.
Definition term321 (x0 : real) (x1 : real) (x2 : nat) := or (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term132 (x0 : nat) := fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y1 : real => (exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ (exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0).
Definition term90 (x0 : nat) (x1 : real) := fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y1 : real => ((real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1))) y0).
Definition term317 (x0 : nat) (x1 : real) (x2 : real) := (real_lt (real_pow x1 x0) (real_pow x2 x0)) \/ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (~ (real_lt x1 x2))).
Definition term149 (x0 : nat) := @eq Prop (exists y0 : real, (exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term148 (x0 : nat) := @eq Prop (exists y0 : real, ((fun y1 : real => exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2)) y0)).
Definition term134 (x0 : nat) := @eq Prop (exists y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1)))).
Definition term133 (x0 : nat) := @eq Prop (exists y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y1 : real => (exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ (exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0)).
Definition term114 (x0 : nat) (x1 : real) := @eq Prop (exists y0 : real, ((real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0))).
Definition term113 (x0 : nat) (x1 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => (real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) y0) \/ ((fun y1 : real => (~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1)) y0)).
Definition term92 (x0 : nat) (x1 : real) := @eq Prop (exists y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (((real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0)))).
Definition term91 (x0 : nat) (x1 : real) := @eq Prop (exists y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y1 : real => ((real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1))) y0)).
Definition term247 (x0 : real) (x1 : real) (x2 : nat) := ((~ (real_le x0 x1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term224 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0).
Definition term42 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0).
Definition term65 (x0 : nat) (x1 : real) := exists y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (((real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0))).
Definition term58 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term196 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term111 (x0 : nat) (x1 : real) (x2 : real) := ((fun y0 : real => (real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) x2) \/ ((fun y0 : real => (~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0)) x2).
Definition term323 (x0 : real) (x1 : real) (x2 : nat) := (~ ((~ (real_lt x0 x1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2)))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term62 (x0 : nat) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow x1 x0) (real_pow y0 x0)) = (real_lt x1 y0)) x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term314 (x0 : nat) (x1 : real) (x2 : real) := (real_lt (real_pow x1 x0) (real_pow x2 x0)) \/ (~ (real_lt x1 x2)).
Definition term103 (x0 : nat) (x1 : real) := fun y0 : real => (real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0)).
Definition term287 (x0 : real) (x1 : real) := imp (real_lt x0 x1).
Definition term227 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)) x0.
Definition term225 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) x0.
Definition term126 (x0 : nat) := exists y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term51 (x0 : nat) (x1 : real) (x2 : real) := ((real_lt (real_pow x1 x0) (real_pow x2 x0)) /\ (~ (real_lt x1 x2))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow x2 x0))) /\ (real_lt x1 x2)).
Definition term159 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((exists y0 : real, exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y0 : real, exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term124 (x0 : nat) (x1 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((exists y0 : real, (real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ (exists y0 : real, (~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0))).
Definition term9 := (~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> False.
Definition term216 (x0 : real) := forall y0 : real, (fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0.
Definition term211 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0.
Definition term78 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : real, forall y3 : real, (Coq.Arith.PeanoNat.Nat.Odd y1) -> (real_lt (real_pow y2 y1) (real_pow y3 y1)) = (real_lt y2 y3)) y0).
Definition term125 (x0 : nat) := fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term316 (x0 : nat) (x1 : real) (x2 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((real_lt (real_pow x1 x0) (real_pow x2 x0)) \/ (~ (real_lt x1 x2))).
Definition term11 := (~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))) -> (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> False.
Definition term229 := fun y0 : real => ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0).
Definition term283 (x0 : real) (x1 : real) := (~ (~ (real_lt x1 x0))) -> ~ (real_le x0 x1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term206 (x0 : real) (x1 : real) := ((fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) x1) /\ ((fun y0 : real => (real_le x0 y0) \/ (real_lt y0 x0)) x1).
Definition term131 (x0 : nat) (x1 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y0 : real => (exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))) x1).
Definition term272 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_lt y0 y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))) \/ (real_lt (real_pow y0 x0) (real_pow y1 x0))) x1.
Definition term269 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))) \/ (real_le (real_pow y0 x0) (real_pow y1 x0))) x1.
Definition term68 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow y0 x0) (real_pow y1 x0)) = (real_lt y0 y1)) x1.
Definition term326 (x0 : real) (x1 : real) := and (~ (~ (real_lt x0 x1))).
Definition term176 (x0 : nat) (x1 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y0 : real => exists y1 : real, ((real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))) x1).
Definition term160 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((exists y1 : real, exists y2 : real, (real_lt (real_pow y1 y0) (real_pow y2 y0)) /\ (~ (real_lt y1 y2))) \/ (exists y1 : real, exists y2 : real, (~ (real_lt (real_pow y1 y0) (real_pow y2 y0))) /\ (real_lt y1 y2))).
Definition term161 := exists y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((exists y1 : real, exists y2 : real, (real_lt (real_pow y1 y0) (real_pow y2 y0)) /\ (~ (real_lt y1 y2))) \/ (exists y1 : real, exists y2 : real, (~ (real_lt (real_pow y1 y0) (real_pow y2 y0))) /\ (real_lt y1 y2))).
Definition term291 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_pow x0 x2) (real_pow x1 x2)) -> ~ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term53 (x0 : nat) := and (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term202 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) x1.
Definition term108 (x0 : nat) (x1 : real) (x2 : real) := or ((real_lt (real_pow x1 x0) (real_pow x2 x0)) /\ (~ (real_lt x1 x2))).
Definition term112 (x0 : nat) (x1 : real) := fun y0 : real => ((fun y1 : real => (real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) y0) \/ ((fun y1 : real => (~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1)) y0).
Definition term259 (x0 : real) (x1 : real) (x2 : nat) := (~ ((real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2))) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term139 (x0 : nat) := exists y0 : real, ((fun y1 : real => exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2)) y0).
Definition term101 (x0 : nat) (x1 : real) := exists y0 : real, ((fun y1 : real => (real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) y0) \/ ((fun y1 : real => (~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1)) y0).
Definition term77 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2)) x0).
Definition term200 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0)).
Definition term285 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term142 (x0 : nat) := fun y0 : real => exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1).
Definition term297 (x0 : real) (x1 : real) (x2 : nat) := ~ ((~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term69 (x0 : nat) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow y0 x0) (real_pow y1 x0)) = (real_lt y0 y1)) x1).
Definition term89 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y0 : real => ((real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0))) x2).
Definition term52 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term39 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term203 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_lt x0 x1)).
Definition term220 := forall y0 : real, (forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) /\ (forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)).
Definition term75 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : real, forall y3 : real, (Coq.Arith.PeanoNat.Nat.Odd y1) -> (real_lt (real_pow y2 y1) (real_pow y3 y1)) = (real_lt y2 y3)) y0).
Definition term256 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_lt x0 x1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term242 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_le x0 x1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term238 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0.
Definition term233 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0.
Definition term306 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (real_le x0 x1).
Definition term274 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_le x0 x1)) \/ ((~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term228 (x0 : real) := ((fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0))) x0) /\ ((fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_lt y1 y0)) x0).
Definition term20 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)).
Definition term249 (x0 : real) (x1 : nat) := fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x1))) \/ (real_le (real_pow x0 x1) (real_pow y0 x1)).
Definition term207 (x0 : real) := fun y0 : real => ((fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ ((fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0).
Definition term215 (x0 : real) := fun y0 : real => (fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term63 (x0 : nat) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow x1 x0) (real_pow y1 x0)) = (real_lt x1 y1)) y0).
Definition term64 (x0 : nat) (x1 : real) := fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (((real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0))).
Definition term197 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term183 (x0 : real) (x1 : real) := or (~ (~ (real_le x0 x1))).
Definition term32 (x0 : real) (x1 : real) (x2 : nat) := ((real_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)) -> real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term45 (x0 : nat) (x1 : real) := fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow x1 x0) (real_pow y0 x0)) = (real_lt x1 y0).
Definition term46 (x0 : nat) (x1 : real) := forall y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_lt (real_pow x1 x0) (real_pow y0 x0)) = (real_lt x1 y0).
Definition term194 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term80 := exists y0 : nat, exists y1 : real, exists y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) /\ (((real_lt (real_pow y1 y0) (real_pow y2 y0)) /\ (~ (real_lt y1 y2))) \/ ((~ (real_lt (real_pow y1 y0) (real_pow y2 y0))) /\ (real_lt y1 y2))).
Definition term50 (x0 : nat) (x1 : real) (x2 : real) := ~ ((real_lt (real_pow x1 x0) (real_pow x2 x0)) = (real_lt x1 x2)).
Definition term275 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term304 (x0 : nat) (x1 : real) (x2 : real) := ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ (~ (real_le (real_pow x1 x0) (real_pow x2 x0)))) -> ~ (real_le x1 x2).
Definition term263 (x0 : real) (x1 : nat) := forall y0 : real, ((~ (real_lt x0 y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x1))) \/ (real_lt (real_pow x0 x1) (real_pow y0 x1)).
Definition term250 (x0 : real) (x1 : nat) := forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x1))) \/ (real_le (real_pow x0 x1) (real_pow y0 x1)).
Definition term26 (x0 : real) (x1 : real) (x2 : nat) := ((real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term289 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_pow x1 x2) (real_pow x0 x2)) -> ~ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term322 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_pow x0 x2) (real_pow x1 x2)) \/ ((~ (real_lt x0 x1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))).
Definition term177 (x0 : nat) := fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((fun y1 : real => exists y2 : real, ((real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ ((~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0).
Definition term246 (x0 : real) (x1 : real) (x2 : nat) := (~ ((real_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2))) \/ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term204 (x0 : real) (x1 : real) := and ((fun y0 : real => (~ (real_le x0 y0)) \/ (~ (real_lt y0 x0))) x1).
Definition term137 (x0 : nat) := exists y0 : real, (exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1)).
Definition term181 (x0 : nat) (x1 : real) := @eq Prop ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y0 : real, ((real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0)))).
Definition term180 (x0 : nat) (x1 : real) := @eq Prop ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y0 : real, (fun y1 : real => ((real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) \/ ((~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1))) y0)).
Definition term175 (x0 : nat) := @eq Prop ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y0 : real, exists y1 : real, ((real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1)))).
Definition term174 (x0 : nat) := @eq Prop ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ (exists y0 : real, (fun y1 : real => exists y2 : real, ((real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ ((~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0)).
Definition term147 (x0 : nat) := fun y0 : real => ((fun y1 : real => exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2)) y0).
Definition term325 (x0 : real) (x1 : real) (x2 : nat) := (~ (~ (real_lt x0 x1))) /\ (~ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))).
Definition term18 := imp (forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)).
Definition term119 (x0 : nat) (x1 : real) := or (exists y0 : real, (real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))).
Definition term154 (x0 : nat) := or (exists y0 : real, exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term74 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term129 (x0 : nat) := fun y0 : real => (exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1)).
Definition term221 := forall y0 : real, ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ (~ (real_lt y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ (real_lt y2 y1)) y0).
Definition term198 (x0 : real) := forall y0 : real, ((fun y1 : real => (~ (real_le x0 y1)) \/ (~ (real_lt y1 x0))) y0) /\ ((fun y1 : real => (real_le x0 y1) \/ (real_lt y1 x0)) y0).
Definition term255 (x0 : real) (x1 : real) (x2 : nat) := ~ ((real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term241 (x0 : real) (x1 : real) (x2 : nat) := ~ ((real_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term109 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => (~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0)) x2.
Definition term140 (x0 : nat) := (exists y0 : real, (fun y1 : real => exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2)) y0).
Definition term102 (x0 : nat) (x1 : real) := (exists y0 : real, (fun y1 : real => (real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1)) y0).
Definition term205 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_lt y0 x0)) x1.
Definition term24 := imp (~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) = (real_lt y1 y2))).
Definition term292 (x0 : Prop) := x0 -> ~ x0.
Definition term223 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (~ (real_lt y1 y0)).
Definition term277 (x0 : real) (x1 : real) (x2 : nat) := (~ (real_lt x0 x1)) \/ ((~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term258 (x0 : real) (x1 : real) (x2 : nat) := or ((~ (real_lt x0 x1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))).
Definition term245 (x0 : real) (x1 : real) (x2 : nat) := or ((~ (real_le x0 x1)) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))).
Definition term122 (x0 : nat) (x1 : real) := exists y0 : real, (~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0).
Definition term144 (x0 : nat) (x1 : real) := or ((fun y0 : real => exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) x1).
Definition term54 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) /\ (~ ((real_lt (real_pow x1 x0) (real_pow x2 x0)) = (real_lt x1 x2))).
Definition term286 (x0 : real) (x1 : real) := imp (~ (~ (real_lt x0 x1))).
Definition term173 (x0 : nat) := exists y0 : real, (fun y1 : real => exists y2 : real, ((real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) \/ ((~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2))) y0.
Definition term156 (x0 : nat) := exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2)) y0.
Definition term151 (x0 : nat) := exists y0 : real, (fun y1 : real => exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) y0.
Definition term165 (x0 : nat) (x1 : real) := @eq Prop ((exists y0 : real, (real_lt (real_pow x1 x0) (real_pow y0 x0)) /\ (~ (real_lt x1 y0))) \/ (exists y0 : real, (~ (real_lt (real_pow x1 x0) (real_pow y0 x0))) /\ (real_lt x1 y0))).
Definition term164 (x0 : nat) (x1 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (real_lt (real_pow x1 x0) (real_pow y1 x0)) /\ (~ (real_lt x1 y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_lt (real_pow x1 x0) (real_pow y1 x0))) /\ (real_lt x1 y1)) y0)).
Definition term163 (x0 : nat) := @eq Prop ((exists y0 : real, exists y1 : real, (real_lt (real_pow y0 x0) (real_pow y1 x0)) /\ (~ (real_lt y0 y1))) \/ (exists y0 : real, exists y1 : real, (~ (real_lt (real_pow y0 x0) (real_pow y1 x0))) /\ (real_lt y0 y1))).
Definition term162 (x0 : nat) := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, (real_lt (real_pow y1 x0) (real_pow y2 x0)) /\ (~ (real_lt y1 y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_lt (real_pow y1 x0) (real_pow y2 x0))) /\ (real_lt y1 y2)) y0)).
