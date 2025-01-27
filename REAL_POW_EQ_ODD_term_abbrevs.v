Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term186 (x0 : real) (x1 : real) (x2 : nat) := (x0 = x1) \/ ((~ ((real_pow x0 x2) = (real_pow x1 x2))) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))).
Definition term152 (x0 : nat) := forall y0 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y1 : real => forall y2 : real, (((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ ((~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0).
Definition term109 (x0 : nat) := forall y0 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y1 : real => (forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ (forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0).
Definition term66 (x0 : nat) (x1 : real) := forall y0 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y1 : real => (((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) /\ ((~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1))) y0).
Definition term169 := fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (((real_pow y1 y0) = (real_pow y2 y0)) \/ (~ (y1 = y2)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((~ ((real_pow y1 y0) = (real_pow y2 y0))) \/ (y1 = y2))).
Definition term60 := fun y0 : nat => forall y1 : real, forall y2 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((((real_pow y1 y0) = (real_pow y2 y0)) \/ (~ (y1 = y2))) /\ ((~ ((real_pow y1 y0) = (real_pow y2 y0))) \/ (y1 = y2))).
Definition term24 := fun y0 : nat => forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2.
Definition term18 := fun y0 : nat => forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2).
Definition term44 (x0 : nat -> Prop) := ~ (all x0).
Definition term28 (x0 : real -> Prop) := ~ (all x0).
Definition term208 := (~ False) -> False.
Definition term4 := (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False.
Definition term63 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term32 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow y0 x0))) -> x1 = y0) x2.
Definition term147 (x0 : nat) (x1 : real) := @eq Prop ((forall y0 : real, ((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ (forall y0 : real, (~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0))).
Definition term146 (x0 : nat) (x1 : real) := @eq Prop ((forall y0 : real, (fun y1 : real => ((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) y0) /\ (forall y0 : real, (fun y1 : real => (~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1)) y0)).
Definition term145 (x0 : nat) := @eq Prop ((forall y0 : real, forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term144 (x0 : nat) := @eq Prop ((forall y0 : real, (fun y1 : real => forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2)) y0)).
Definition term171 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (((real_pow y1 y0) = (real_pow y2 y0)) \/ (~ (y1 = y2)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((~ ((real_pow y1 y0) = (real_pow y2 y0))) \/ (y1 = y2)))) x0.
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2) x0.
Definition term35 (x0 : nat) (x1 : real) := fun y0 : real => ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow y0 x0))) /\ (~ (x1 = y0)).
Definition term19 (x0 : nat) (x1 : real) (x2 : real) := ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow x2 x0))) -> x1 = x2.
Definition term199 (x0 : Prop) := ~ (~ x0).
Definition term160 (x0 : nat) := fun y0 : real => (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y1 : real, (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term136 (x0 : nat) := and (forall y0 : real, forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))).
Definition term86 (x0 : nat) (x1 : real) := fun y0 : real => (~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0).
Definition term192 (x0 : real) (x1 : real) (x2 : nat) := (x0 = x1) \/ ((~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2)))).
Definition term178 (x0 : real) (x1 : real) (x2 : nat) := (~ ((real_pow x0 x2) = (real_pow x1 x2))) -> (real_pow x0 x2) = (real_pow x1 x2).
Definition term201 (x0 : nat) := and (~ (~ (Coq.Arith.PeanoNat.Nat.Odd x0))).
Definition term101 (x0 : nat) (x1 : real) := and (forall y0 : real, ((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))).
Definition term56 (x0 : nat) (x1 : real) := fun y0 : real => (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0))).
Definition term87 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => ((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) x2.
Definition term62 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term117 (x0 : nat) := fun y0 : real => (fun y1 : real => (forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ (forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0.
Definition term135 (x0 : nat) := and (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) y0).
Definition term100 (x0 : nat) (x1 : real) := and (forall y0 : real, (fun y1 : real => ((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term30 (x0 : nat) (x1 : real) := ~ (forall y0 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow y0 x0))) -> x1 = y0).
Definition term205 (x0 : real) (x1 : real) (x2 : nat) := imp ((Coq.Arith.PeanoNat.Nat.Odd x2) /\ ((real_pow x0 x2) = (real_pow x1 x2))).
Definition term111 (x0 : nat) := fun y0 : real => (forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1)).
Definition term207 (x0 : real) (x1 : real) := (x0 = x1) -> False.
Definition term20 (x0 : nat) (x1 : real) := fun y0 : real => ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow y0 x0))) -> x1 = y0.
Definition term140 (x0 : nat) := (forall y0 : real, forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1)).
Definition term13 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2).
Definition term193 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term122 (x0 : nat) := (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2)) y0).
Definition term84 (x0 : nat) (x1 : real) := (forall y0 : real, (fun y1 : real => ((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) y0) /\ (forall y0 : real, (fun y1 : real => (~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1)) y0).
Definition term65 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (forall y0 : real, x1 y0).
Definition term9 := ~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)).
Definition term3 := ~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2).
Definition term204 (x0 : real) (x1 : real) (x2 : nat) := imp (~ ((~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2))))).
Definition term53 (x0 : nat) := or (~ (Coq.Arith.PeanoNat.Nat.Odd x0)).
Definition term188 (x0 : real) (x1 : real) (x2 : nat) := @eq Prop ((x0 = x1) \/ ((~ ((real_pow x0 x2) = (real_pow x1 x2))) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2)))).
Definition term177 (x0 : Prop) := (~ x0) -> x0.
Definition term159 (x0 : nat) := fun y0 : real => (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y1 : real => forall y2 : real, (((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ ((~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0).
Definition term151 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y0 : real, (fun y1 : real => forall y2 : real, (((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ ((~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0).
Definition term110 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y0 : real, (fun y1 : real => (forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ (forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0).
Definition term67 (x0 : nat) (x1 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y0 : real, (fun y1 : real => (((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) /\ ((~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1))) y0).
Definition term154 (x0 : nat) := fun y0 : real => (fun y1 : real => forall y2 : real, (((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ ((~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0.
Definition term137 (x0 : nat) := fun y0 : real => (fun y1 : real => forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2)) y0.
Definition term132 (x0 : nat) := fun y0 : real => (fun y1 : real => forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) y0.
Definition term196 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term85 (x0 : nat) (x1 : real) := fun y0 : real => ((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0)).
Definition term71 (x0 : nat) (x1 : real) (x2 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y0 : real => (((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0))) x2).
Definition term168 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term149 (x0 : nat) := forall y0 : real, forall y1 : real, (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1)).
Definition term139 (x0 : nat) := forall y0 : real, forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1).
Definition term134 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1)).
Definition term59 (x0 : nat) := forall y0 : real, forall y1 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term23 (x0 : nat) := forall y0 : real, forall y1 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow y0 x0) = (real_pow y1 x0))) -> y0 = y1.
Definition term17 (x0 : nat) := forall y0 : real, forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow y0 x0) = (real_pow y1 x0)) = (y0 = y1).
Definition term173 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0)))) x2.
Definition term77 (x0 : nat) (x1 : real) := forall y0 : real, (((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0)).
Definition term43 (x0 : nat) := exists y0 : real, exists y1 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow y0 x0) = (real_pow y1 x0))) /\ (~ (y0 = y1)).
Definition term184 (x0 : real) (x1 : real) (x2 : nat) := or (~ ((real_pow x0 x2) = (real_pow x1 x2))).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term206 (x0 : real) (x1 : real) := (~ (x0 = x1)) -> x0 = x1.
Definition term88 (x0 : nat) (x1 : real) (x2 : real) := ((real_pow x1 x0) = (real_pow x2 x0)) \/ (~ (x1 = x2)).
Definition term180 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term107 (x0 : nat) := fun y0 : real => (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term38 (x0 : nat) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow y1 x0) = (real_pow y2 x0))) -> y1 = y2) y0).
Definition term31 (x0 : nat) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow y1 x0))) -> x1 = y1) y0).
Definition term120 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y0 : real, (forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term78 (x0 : nat) (x1 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y0 : real, (((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0))).
Definition term163 (x0 : nat) (x1 : real) := @eq Prop ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y0 : real, (((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0)))).
Definition term162 (x0 : nat) (x1 : real) := @eq Prop ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y0 : real, (fun y1 : real => (((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) /\ ((~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1))) y0)).
Definition term157 (x0 : nat) := @eq Prop ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y0 : real, forall y1 : real, (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1)))).
Definition term156 (x0 : nat) := @eq Prop ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y0 : real, (fun y1 : real => forall y2 : real, (((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ ((~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0)).
Definition term57 (x0 : nat) (x1 : real) := forall y0 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0))).
Definition term64 (x0 : Prop) (x1 : real -> Prop) := forall y0 : real, x0 \/ (x1 y0).
Definition term50 := fun y0 : nat => exists y1 : real, exists y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) /\ (~ (y1 = y2)).
Definition term165 (x0 : nat) (x1 : real) := fun y0 : real => ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0))).
Definition term41 (x0 : nat) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow y1 x0) = (real_pow y2 x0))) -> y1 = y2) y0).
Definition term131 (x0 : nat) := @eq Prop (forall y0 : real, (forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term130 (x0 : nat) := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2)) y0)).
Definition term116 (x0 : nat) := @eq Prop (forall y0 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1)))).
Definition term115 (x0 : nat) := @eq Prop (forall y0 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y1 : real => (forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ (forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0)).
Definition term96 (x0 : nat) (x1 : real) := @eq Prop (forall y0 : real, (((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0))).
Definition term95 (x0 : nat) (x1 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => ((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) y0) /\ ((fun y1 : real => (~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1)) y0)).
Definition term74 (x0 : nat) (x1 : real) := @eq Prop (forall y0 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0)))).
Definition term73 (x0 : nat) (x1 : real) := @eq Prop (forall y0 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y1 : real => (((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) /\ ((~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1))) y0)).
Definition term42 (x0 : nat) := fun y0 : real => exists y1 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow y0 x0) = (real_pow y1 x0))) /\ (~ (y0 = y1)).
Definition term167 (x0 : nat) := fun y0 : real => forall y1 : real, ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term148 (x0 : nat) := fun y0 : real => forall y1 : real, (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1)).
Definition term58 (x0 : nat) := fun y0 : real => forall y1 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term16 (x0 : nat) := fun y0 : real => forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow y0 x0) = (real_pow y1 x0)) = (y0 = y1).
Definition term8 := (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False.
Definition term174 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term176 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> Coq.Arith.PeanoNat.Nat.Odd x0.
Definition term200 (x0 : nat) := ~ (~ (Coq.Arith.PeanoNat.Nat.Odd x0)).
Definition term37 (x0 : nat) := ~ (forall y0 : real, forall y1 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow y0 x0) = (real_pow y1 x0))) -> y0 = y1).
Definition term112 (x0 : nat) (x1 : real) := (fun y0 : real => (forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))) x1.
Definition term90 (x0 : nat) (x1 : real) (x2 : real) := and (((real_pow x1 x0) = (real_pow x2 x0)) \/ (~ (x1 = x2))).
Definition term175 (x0 : nat) (x1 : real) (x2 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((~ ((real_pow x1 x0) = (real_pow x2 x0))) \/ (x1 = x2)).
Definition term6 := (((~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False.
Definition term128 (x0 : nat) (x1 : real) := ((fun y0 : real => forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) x1) /\ ((fun y0 : real => forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1)) x1).
Definition term91 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => (~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0)) x2.
Definition term36 (x0 : nat) (x1 : real) := exists y0 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow y0 x0))) /\ (~ (x1 = y0)).
Definition term179 (x0 : real) (x1 : real) (x2 : nat) := ~ ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term195 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term105 (x0 : nat) (x1 : real) := (forall y0 : real, ((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ (forall y0 : real, (~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0)).
Definition term170 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ (((real_pow y1 y0) = (real_pow y2 y0)) \/ (~ (y1 = y2)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((~ ((real_pow y1 y0) = (real_pow y2 y0))) \/ (y1 = y2))).
Definition term61 := forall y0 : nat, forall y1 : real, forall y2 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((((real_pow y1 y0) = (real_pow y2 y0)) \/ (~ (y1 = y2))) /\ ((~ ((real_pow y1 y0) = (real_pow y2 y0))) \/ (y1 = y2))).
Definition term10 := forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2).
Definition term1 := forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2.
Definition term158 (x0 : nat) (x1 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y0 : real => forall y1 : real, (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))) x1).
Definition term69 (x0 : nat) (x1 : real) := fun y0 : real => (((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0)).
Definition term97 (x0 : nat) (x1 : real) := fun y0 : real => (fun y1 : real => ((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) y0.
Definition term92 (x0 : nat) (x1 : real) (x2 : real) := (~ ((real_pow x1 x0) = (real_pow x2 x0))) \/ (x1 = x2).
Definition term124 (x0 : nat) := fun y0 : real => forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1).
Definition term22 (x0 : nat) := fun y0 : real => forall y1 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow y0 x0) = (real_pow y1 x0))) -> y0 = y1.
Definition term29 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term81 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term33 (x0 : nat) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow y0 x0))) -> x1 = y0) x2).
Definition term187 (x0 : nat) (x1 : real) (x2 : real) := @eq Prop ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((~ ((real_pow x1 x0) = (real_pow x2 x0))) \/ (x1 = x2))).
Definition term161 (x0 : nat) := forall y0 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y1 : real, (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term2 := (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> False.
Definition term118 (x0 : nat) := forall y0 : real, (fun y1 : real => (forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ (forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0.
Definition term103 (x0 : nat) (x1 : real) := forall y0 : real, (fun y1 : real => (~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1)) y0.
Definition term98 (x0 : nat) (x1 : real) := forall y0 : real, (fun y1 : real => ((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) y0.
Definition term76 (x0 : nat) (x1 : real) := forall y0 : real, (fun y1 : real => (((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) /\ ((~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1))) y0.
Definition term49 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : real, forall y3 : real, ((Coq.Arith.PeanoNat.Nat.Odd y1) /\ ((real_pow y2 y1) = (real_pow y3 y1))) -> y2 = y3) y0).
Definition term191 (x0 : real) (x1 : real) := or (x0 = x1).
Definition term182 (x0 : nat) (x1 : real) (x2 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (x1 = x2).
Definition term129 (x0 : nat) := fun y0 : real => ((fun y1 : real => forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2)) y0).
Definition term89 (x0 : nat) (x1 : real) (x2 : real) := and ((fun y0 : real => ((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) x2).
Definition term164 (x0 : nat) (x1 : real) (x2 : real) := ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (((real_pow x1 x0) = (real_pow x2 x0)) \/ (~ (x1 = x2)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((~ ((real_pow x1 x0) = (real_pow x2 x0))) \/ (x1 = x2))).
Definition term93 (x0 : nat) (x1 : real) (x2 : real) := ((fun y0 : real => ((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) x2) /\ ((fun y0 : real => (~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0)) x2).
Definition term55 (x0 : nat) (x1 : real) (x2 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((((real_pow x1 x0) = (real_pow x2 x0)) \/ (~ (x1 = x2))) /\ ((~ ((real_pow x1 x0) = (real_pow x2 x0))) \/ (x1 = x2))).
Definition term126 (x0 : nat) (x1 : real) := and ((fun y0 : real => forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) x1).
Definition term172 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1)))) x1.
Definition term153 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))) x1.
Definition term127 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1)) x1.
Definition term125 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) x1.
Definition term39 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow y0 x0) = (real_pow y1 x0))) -> y0 = y1) x1.
Definition term25 (x0 : nat) (x1 : real) (x2 : real) := ~ (((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow x2 x0))) -> x1 = x2).
Definition term202 (x0 : nat) := and (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term150 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (forall y0 : real, forall y1 : real, (((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ ((~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term48 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2) x0).
Definition term52 (x0 : nat) (x1 : real) (x2 : real) := (((real_pow x1 x0) = (real_pow x2 x0)) \/ (~ (x1 = x2))) /\ ((~ ((real_pow x1 x0) = (real_pow x2 x0))) \/ (x1 = x2)).
Definition term143 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((forall y1 : real, forall y2 : real, ((real_pow y1 y0) = (real_pow y2 y0)) \/ (~ (y1 = y2))) /\ (forall y1 : real, forall y2 : real, (~ ((real_pow y1 y0) = (real_pow y2 y0))) \/ (y1 = y2))).
Definition term113 (x0 : nat) (x1 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y0 : real => (forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))) x1).
Definition term108 (x0 : nat) := forall y0 : real, (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term40 (x0 : nat) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow y0 x0) = (real_pow y1 x0))) -> y0 = y1) x1).
Definition term190 (x0 : real) (x1 : real) (x2 : nat) := (~ ((real_pow x0 x2) = (real_pow x1 x2))) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term119 (x0 : nat) := forall y0 : real, (forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1)).
Definition term104 (x0 : nat) (x1 : real) := forall y0 : real, (~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0).
Definition term21 (x0 : nat) (x1 : real) := forall y0 : real, ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow y0 x0))) -> x1 = y0.
Definition term194 (x0 : nat) (x1 : real) (x2 : real) := (~ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (~ ((real_pow x1 x0) = (real_pow x2 x0))))) -> x1 = x2.
Definition term114 (x0 : nat) := fun y0 : real => (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y1 : real => (forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ (forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0).
Definition term72 (x0 : nat) (x1 : real) := fun y0 : real => (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((fun y1 : real => (((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) /\ ((~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1))) y0).
Definition term46 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : real, forall y3 : real, ((Coq.Arith.PeanoNat.Nat.Odd y1) /\ ((real_pow y2 y1) = (real_pow y3 y1))) -> y2 = y3) y0).
Definition term75 (x0 : nat) (x1 : real) := fun y0 : real => (fun y1 : real => (((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) /\ ((~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1))) y0.
Definition term12 := (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> ~ (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)).
Definition term155 (x0 : nat) := forall y0 : real, (fun y1 : real => forall y2 : real, (((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) /\ ((~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2))) y0.
Definition term138 (x0 : nat) := forall y0 : real, (fun y1 : real => forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2)) y0.
Definition term133 (x0 : nat) := forall y0 : real, (fun y1 : real => forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) y0.
Definition term94 (x0 : nat) (x1 : real) := fun y0 : real => ((fun y1 : real => ((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) y0) /\ ((fun y1 : real => (~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1)) y0).
Definition term102 (x0 : nat) (x1 : real) := fun y0 : real => (fun y1 : real => (~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1)) y0.
Definition term142 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) \/ ((forall y1 : real, forall y2 : real, ((real_pow y1 y0) = (real_pow y2 y0)) \/ (~ (y1 = y2))) /\ (forall y1 : real, forall y2 : real, (~ ((real_pow y1 y0) = (real_pow y2 y0))) \/ (y1 = y2))).
Definition term166 (x0 : nat) (x1 : real) := forall y0 : real, ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0)))) /\ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0))).
Definition term34 (x0 : nat) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow y1 x0))) -> x1 = y1) y0).
Definition term82 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term14 (x0 : nat) (x1 : real) := fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow y0 x0)) = (x1 = y0).
Definition term15 (x0 : nat) (x1 : real) := forall y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow y0 x0)) = (x1 = y0).
Definition term198 (x0 : real) (x1 : real) (x2 : nat) := (~ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))) /\ (~ (~ ((real_pow x0 x2) = (real_pow x1 x2)))).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term51 := exists y0 : nat, exists y1 : real, exists y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) /\ (~ (y1 = y2)).
Definition term181 (x0 : nat) (x1 : real) (x2 : real) := (~ ((real_pow x1 x0) = (real_pow x2 x0))) \/ ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (x1 = x2)).
Definition term68 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term5 := ((~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False.
Definition term185 (x0 : real) (x1 : real) (x2 : nat) := (~ ((real_pow x0 x2) = (real_pow x1 x2))) \/ ((x0 = x1) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2))).
Definition term7 := (((~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False) -> ((~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False) -> (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)) -> (forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2)) -> False.
Definition term54 (x0 : nat) (x1 : real) (x2 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ (((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)).
Definition term183 (x0 : real) (x1 : real) (x2 : nat) := (x0 = x1) \/ (~ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term45 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term26 (x0 : nat) (x1 : real) (x2 : real) := ((Coq.Arith.PeanoNat.Nat.Odd x0) /\ ((real_pow x1 x0) = (real_pow x2 x0))) /\ (~ (x1 = x2)).
Definition term99 (x0 : nat) (x1 : real) := forall y0 : real, ((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0)).
Definition term121 (x0 : nat) := forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_pow y1 x0) = (real_pow y2 x0)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ ((real_pow y1 x0) = (real_pow y2 x0))) \/ (y1 = y2)) y0).
Definition term83 (x0 : nat) (x1 : real) := forall y0 : real, ((fun y1 : real => ((real_pow x1 x0) = (real_pow y1 x0)) \/ (~ (x1 = y1))) y0) /\ ((fun y1 : real => (~ ((real_pow x1 x0) = (real_pow y1 x0))) \/ (x1 = y1)) y0).
Definition term197 (x0 : real) (x1 : real) (x2 : nat) := ~ ((~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2)))).
Definition term141 (x0 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((forall y0 : real, forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, (~ ((real_pow y0 x0) = (real_pow y1 x0))) \/ (y0 = y1))).
Definition term106 (x0 : nat) (x1 : real) := (~ (Coq.Arith.PeanoNat.Nat.Odd x0)) \/ ((forall y0 : real, ((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ (forall y0 : real, (~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0))).
Definition term189 (x0 : real) (x1 : real) (x2 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Odd x2)) \/ (~ ((real_pow x0 x2) = (real_pow x1 x2))).
Definition term11 := imp (~ (forall y0 : nat, forall y1 : real, forall y2 : real, ((Coq.Arith.PeanoNat.Nat.Odd y0) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> y1 = y2)).
Definition term123 (x0 : nat) := fun y0 : real => forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) \/ (~ (y0 = y1)).
Definition term27 (x0 : real) (x1 : real) (x2 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x2) /\ ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term203 (x0 : real) (x1 : real) (x2 : nat) := ~ (~ ((real_pow x0 x2) = (real_pow x1 x2))).
Definition term70 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => (((real_pow x1 x0) = (real_pow y0 x0)) \/ (~ (x1 = y0))) /\ ((~ ((real_pow x1 x0) = (real_pow y0 x0))) \/ (x1 = y0))) x2.
