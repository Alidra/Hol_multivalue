Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term86 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term37 (x0 : nat) := Peano.le (S (Nat.add x0 x0)) 0.
Definition term67 (x0 : nat) (x1 : nat) := ((Nat.add x0 x0) = (S (Nat.add x1 x1))) \/ (Peano.le (Nat.add x0 x0) (Nat.add x1 x1)).
Definition term72 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term146 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term288 (x0 : nat) := fun y0 : nat => (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term205 (x0 : nat) (x1 : nat) := ((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 x1).
Definition term130 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 x1).
Definition term297 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.mul (S (NUMERAL (BIT1 0))) x0).
Definition term306 := Coq.Arith.PeanoNat.Nat.Even (S (NUMERAL (BIT1 0))).
Definition term217 (x0 : nat) (x1 : nat) := or ((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1))).
Definition term69 (x0 : nat) (x1 : nat) := or ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term70 (x0 : nat) (x1 : nat) := ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term278 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term218 (x0 : nat) (x1 : nat) := ((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1))) \/ (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 x1)).
Definition term137 (x0 : nat) (x1 : nat) := ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 x1)).
Definition term154 := True /\ ((forall y0 : nat, forall y1 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1))))).
Definition term16 := True /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))))).
Definition term199 (x0 : nat) := @eq Prop (((S (NUMERAL (BIT1 0))) = 0) \/ (x0 = 0)).
Definition term124 (x0 : nat) := @eq Prop (((NUMERAL (BIT0 (BIT1 0))) = 0) \/ (x0 = 0)).
Definition term42 (x0 : nat) := ~ ((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = 0).
Definition term195 := @eq nat (S (NUMERAL (BIT1 0))).
Definition term11 := fun y0 : nat => Peano.le 0 (S (Nat.add y0 y0)).
Definition term49 (x0 : nat) := Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term120 := (forall y0 : nat, ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ~ ((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = 0)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)))))).
Definition term23 := (forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1)))))).
Definition term22 := (forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)) /\ ((forall y0 : nat, Peano.le 0 (Nat.add y0 y0)) /\ ((forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1)))))))).
Definition term17 := (forall y0 : nat, Peano.le 0 (Nat.add y0 y0)) /\ ((forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1)))))).
Definition term203 := or ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term214 (x0 : nat) := Nat.mul (S (NUMERAL (BIT1 0))) x0.
Definition term294 (x0 : nat) (x1 : nat) := ~ ((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1))).
Definition term33 := fun y0 : nat => ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = 0) = (y0 = 0).
Definition term6 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term313 := or (Coq.Arith.PeanoNat.Nat.Even (S (NUMERAL (BIT1 0)))).
Definition term104 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (S (Nat.add x0 x0)) (S (Nat.add x1 x1))).
Definition term129 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term264 (x0 : nat) (x1 : nat) := ((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1))) \/ (Peano.le x0 x1).
Definition term284 := (forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ (forall y0 : nat, forall y1 : nat, ((y0 = y1) \/ (Peano.lt y0 y1)) = (Peano.le y0 y1)).
Definition term243 := (forall y0 : nat, forall y1 : nat, ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (Nat.mul (S (NUMERAL (BIT1 0))) y1)) \/ ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1)).
Definition term189 := (forall y0 : nat, forall y1 : nat, ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1)).
Definition term170 := (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)).
Definition term151 := (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)).
Definition term115 := (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)).
Definition term114 := (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1)).
Definition term305 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term213 := Nat.mul (S (NUMERAL (BIT1 0))).
Definition term53 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term280 (x0 : nat) := forall y0 : nat, ((x0 = y0) \/ (Peano.lt x0 y0)) = (Peano.le x0 y0).
Definition term267 (x0 : nat) := forall y0 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y0))) \/ (Peano.le x0 y0)) = (Peano.le x0 y0).
Definition term240 (x0 : nat) := forall y0 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (Nat.mul (S (NUMERAL (BIT1 0))) y0)) \/ ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 y0))) = (Peano.le x0 y0).
Definition term232 (x0 : nat) := forall y0 : nat, ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 y0)) = (Peano.lt x0 y0).
Definition term221 (x0 : nat) := forall y0 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y0))) \/ (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 y0))) = (Peano.le x0 y0).
Definition term208 (x0 : nat) := forall y0 : nat, (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le x0 y0).
Definition term186 (x0 : nat) := forall y0 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) \/ ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 y0))) = (Peano.le x0 y0).
Definition term179 (x0 : nat) := forall y0 : nat, ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 y0)) = (Peano.lt x0 y0).
Definition term167 (x0 : nat) := forall y0 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) \/ (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) = (Peano.le x0 y0).
Definition term160 (x0 : nat) := forall y0 : nat, (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (Peano.lt x0 y0).
Definition term148 (x0 : nat) := forall y0 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) = (Peano.le x0 y0).
Definition term140 (x0 : nat) := forall y0 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 y0))) = (Peano.le x0 y0).
Definition term133 (x0 : nat) := forall y0 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le x0 y0).
Definition term109 (x0 : nat) := forall y0 : nat, (((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) = (Peano.le x0 y0).
Definition term108 (x0 : nat) := forall y0 : nat, (Peano.le (S (Nat.add x0 x0)) (S (Nat.add y0 y0))) = (Peano.le x0 y0).
Definition term92 (x0 : nat) := forall y0 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (Peano.lt x0 y0).
Definition term91 (x0 : nat) := forall y0 : nat, (Peano.le (S (Nat.add x0 x0)) (Nat.add y0 y0)) = (Peano.lt x0 y0).
Definition term76 (x0 : nat) := forall y0 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) = (Peano.le x0 y0).
Definition term75 (x0 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x0) (S (Nat.add y0 y0))) = (Peano.le x0 y0).
Definition term57 (x0 : nat) := forall y0 : nat, (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (Peano.le x0 y0).
Definition term56 (x0 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x0) (Nat.add y0 y0)) = (Peano.le x0 y0).
Definition term102 (x0 : nat) (x1 : nat) := or ((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term101 (x0 : nat) (x1 : nat) := or ((S (Nat.add x0 x0)) = (S (Nat.add x1 x1))).
Definition term310 := ~ (Coq.Arith.PeanoNat.Nat.Even (Nat.add 0 0)).
Definition term165 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) \/ (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term39 (x0 : nat) := @eq nat (S (Nat.add x0 x0)).
Definition term99 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.add x0 x0)) (S (Nat.add x1 x1)).
Definition term194 := @eq nat (NUMERAL (BIT0 (BIT1 0))).
Definition term239 (x0 : nat) := fun y0 : nat => (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (Nat.mul (S (NUMERAL (BIT1 0))) y0)) \/ ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 y0))) = (Peano.le x0 y0).
Definition term220 (x0 : nat) := fun y0 : nat => (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y0))) \/ (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 y0))) = (Peano.le x0 y0).
Definition term185 (x0 : nat) := fun y0 : nat => (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) \/ ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 y0))) = (Peano.le x0 y0).
Definition term166 (x0 : nat) := fun y0 : nat => (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) \/ (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) = (Peano.le x0 y0).
Definition term147 (x0 : nat) := fun y0 : nat => (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) = (Peano.le x0 y0).
Definition term139 (x0 : nat) := fun y0 : nat => (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 y0))) = (Peano.le x0 y0).
Definition term107 (x0 : nat) := fun y0 : nat => (((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) = (Peano.le x0 y0).
Definition term74 (x0 : nat) := fun y0 : nat => (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) = (Peano.le x0 y0).
Definition term300 (x0 : nat) (x1 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Even (Nat.mul (S (NUMERAL (BIT1 0))) x0)) = (Coq.Arith.PeanoNat.Nat.Even (S (Nat.mul (S (NUMERAL (BIT1 0))) x1)))).
Definition term12 := forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0)).
Definition term287 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1))).
Definition term286 (x0 : nat) (x1 : nat) := ((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term47 := and (forall y0 : nat, ~ ((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = 0)).
Definition term18 := and (forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)).
Definition term157 (x0 : nat) (x1 : nat) := Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term106 (x0 : nat) := fun y0 : nat => (Peano.le (S (Nat.add x0 x0)) (S (Nat.add y0 y0))) = (Peano.le x0 y0).
Definition term73 (x0 : nat) := fun y0 : nat => (Peano.le (Nat.add x0 x0) (S (Nat.add y0 y0))) = (Peano.le x0 y0).
Definition term88 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term83 (x0 : nat) := Peano.le (S (Nat.add x0 x0)).
Definition term32 := fun y0 : nat => (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0).
Definition term41 (x0 : nat) := ~ (Peano.le (S (Nat.add x0 x0)) 0).
Definition term30 (x0 : nat) := @eq Prop (Peano.le (Nat.add x0 x0) 0).
Definition term200 := fun y0 : nat => (((S (NUMERAL (BIT1 0))) = 0) \/ (y0 = 0)) = (y0 = 0).
Definition term125 := fun y0 : nat => (((NUMERAL (BIT0 (BIT1 0))) = 0) \/ (y0 = 0)) = (y0 = 0).
Definition term250 := Nat.add (BIT1 0).
Definition term273 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = x2).
Definition term315 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (Nat.mul (S (NUMERAL (BIT1 0))) x0)).
Definition term9 (x0 : nat) := Peano.le 0 (S (Nat.add x0 x0)).
Definition term1 (x0 : nat) := Peano.le 0 (Nat.add x0 x0).
Definition term50 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 x0) (Nat.add x1 x1).
Definition term308 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL (BIT1 0)).
Definition term281 := fun y0 : nat => forall y1 : nat, ((y0 = y1) \/ (Peano.lt y0 y1)) = (Peano.le y0 y1).
Definition term268 := fun y0 : nat => forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (Peano.le y0 y1)) = (Peano.le y0 y1).
Definition term241 := fun y0 : nat => forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (Nat.mul (S (NUMERAL (BIT1 0))) y1)) \/ ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1).
Definition term233 := fun y0 : nat => forall y1 : nat, ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1).
Definition term222 := fun y0 : nat => forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1).
Definition term209 := fun y0 : nat => forall y1 : nat, (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1).
Definition term187 := fun y0 : nat => forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1).
Definition term180 := fun y0 : nat => forall y1 : nat, ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1).
Definition term168 := fun y0 : nat => forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1).
Definition term161 := fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1).
Definition term149 := fun y0 : nat => forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1).
Definition term141 := fun y0 : nat => forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1).
Definition term134 := fun y0 : nat => forall y1 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1).
Definition term111 := fun y0 : nat => forall y1 : nat, (((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1).
Definition term110 := fun y0 : nat => forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1).
Definition term94 := fun y0 : nat => forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1).
Definition term93 := fun y0 : nat => forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1).
Definition term78 := fun y0 : nat => forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1).
Definition term77 := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1).
Definition term59 := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.le y0 y1).
Definition term58 := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1).
Definition term260 (x0 : nat) := False \/ (x0 = 0).
Definition term245 := (forall y0 : nat, forall y1 : nat, (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (Nat.mul (S (NUMERAL (BIT1 0))) y1)) \/ ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1)))).
Definition term191 := (forall y0 : nat, forall y1 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1)))).
Definition term172 := (forall y0 : nat, forall y1 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)))).
Definition term153 := (forall y0 : nat, forall y1 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)))).
Definition term118 := (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)))).
Definition term14 := (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1)))).
Definition term277 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term10 (x0 : nat) := S (Nat.add x0 x0).
Definition term46 := forall y0 : nat, ~ ((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = 0).
Definition term45 := forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0).
Definition term216 (x0 : nat) := S (Nat.mul (S (NUMERAL (BIT1 0))) x0).
Definition term38 (x0 : nat) := S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term285 := True /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ (forall y0 : nat, forall y1 : nat, ((y0 = y1) \/ (Peano.lt y0 y1)) = (Peano.le y0 y1))).
Definition term24 := (Peano.le 0 0) /\ ((forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)) /\ ((forall y0 : nat, Peano.le 0 (Nat.add y0 y0)) /\ ((forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))))))))).
Definition term212 := Nat.mul (NUMERAL (BIT0 (BIT1 0))).
Definition term244 := (forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (Nat.mul (S (NUMERAL (BIT1 0))) y1)) \/ ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1))).
Definition term190 := (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1))).
Definition term171 := (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1))).
Definition term152 := (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1))).
Definition term117 := (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1))).
Definition term116 := (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))).
Definition term66 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 x0) (S (Nat.add x1 x1)).
Definition term27 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term0 := and (Peano.le 0 0).
Definition term119 := (forall y0 : nat, ~ ((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = 0)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1))))).
Definition term20 := (forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))))).
Definition term230 (x0 : nat) (x1 : nat) := @eq Prop ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 x1)).
Definition term177 (x0 : nat) (x1 : nat) := @eq Prop ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 x1)).
Definition term215 (x0 : nat) := @eq nat (Nat.mul (S (NUMERAL (BIT1 0))) x0).
Definition term29 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term4 := forall y0 : nat, Peano.le 0 (Nat.add y0 y0).
Definition term28 (x0 : nat) := @eq nat (Nat.add x0 x0).
Definition term202 := and (forall y0 : nat, (((S (NUMERAL (BIT1 0))) = 0) \/ (y0 = 0)) = (y0 = 0)).
Definition term127 := and (forall y0 : nat, (((NUMERAL (BIT0 (BIT1 0))) = 0) \/ (y0 = 0)) = (y0 = 0)).
Definition term36 := and (forall y0 : nat, ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = 0) = (y0 = 0)).
Definition term21 := and (forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0)).
Definition term13 := and (forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))).
Definition term8 := and (forall y0 : nat, Peano.le 0 (Nat.add y0 y0)).
Definition term198 (x0 : nat) := ((S (NUMERAL (BIT1 0))) = 0) \/ (x0 = 0).
Definition term122 (x0 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = 0) \/ (x0 = 0).
Definition term272 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term204 := or ((S (NUMERAL (BIT1 0))) = (NUMERAL 0)).
Definition term283 := True /\ (forall y0 : nat, forall y1 : nat, ((y0 = y1) \/ (Peano.lt y0 y1)) = (Peano.le y0 y1)).
Definition term275 (x0 : nat) (x1 : nat) := False \/ (x0 = x1).
Definition term258 := @eq nat (S (S 0)).
Definition term121 (x0 : nat) (x1 : nat) := (x0 = 0) \/ (x1 = 0).
Definition term254 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term87 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (S (Nat.add x0 x0)) (Nat.add x1 x1)).
Definition term304 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (S x0).
Definition term251 := Nat.add (S 0).
Definition term35 := forall y0 : nat, ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = 0) = (y0 = 0).
Definition term34 := forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0).
Definition term291 := forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term282 := forall y0 : nat, forall y1 : nat, ((y0 = y1) \/ (Peano.lt y0 y1)) = (Peano.le y0 y1).
Definition term269 := forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (Peano.le y0 y1)) = (Peano.le y0 y1).
Definition term242 := forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (Nat.mul (S (NUMERAL (BIT1 0))) y1)) \/ ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1).
Definition term234 := forall y0 : nat, forall y1 : nat, ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1).
Definition term223 := forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1).
Definition term210 := forall y0 : nat, forall y1 : nat, (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1).
Definition term188 := forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1).
Definition term181 := forall y0 : nat, forall y1 : nat, ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1).
Definition term169 := forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1).
Definition term162 := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1).
Definition term150 := forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1).
Definition term142 := forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1).
Definition term135 := forall y0 : nat, forall y1 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1).
Definition term113 := forall y0 : nat, forall y1 : nat, (((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1).
Definition term112 := forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1).
Definition term96 := forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1).
Definition term95 := forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1).
Definition term80 := forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1).
Definition term79 := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1).
Definition term61 := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.le y0 y1).
Definition term60 := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1).
Definition term298 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (S (Nat.mul (S (NUMERAL (BIT1 0))) x0)).
Definition term25 := True /\ ((forall y0 : nat, (Peano.le (Nat.add y0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))))))).
Definition term68 (x0 : nat) (x1 : nat) := or ((Nat.add x0 x0) = (S (Nat.add x1 x1))).
Definition term197 := or ((S (NUMERAL (BIT1 0))) = 0).
Definition term196 := or ((NUMERAL (BIT0 (BIT1 0))) = 0).
Definition term231 (x0 : nat) := fun y0 : nat => ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 y0)) = (Peano.lt x0 y0).
Definition term178 (x0 : nat) := fun y0 : nat => ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 y0)) = (Peano.lt x0 y0).
Definition term159 (x0 : nat) := fun y0 : nat => (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (Peano.lt x0 y0).
Definition term90 (x0 : nat) := fun y0 : nat => (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (Peano.lt x0 y0).
Definition term89 (x0 : nat) := fun y0 : nat => (Peano.le (S (Nat.add x0 x0)) (Nat.add y0 y0)) = (Peano.lt x0 y0).
Definition term238 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (Nat.mul (S (NUMERAL (BIT1 0))) x1)) \/ ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 x1))).
Definition term184 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) \/ ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 x1))).
Definition term5 := forall y0 : nat, True.
Definition term193 := S (NUMERAL (BIT1 0)).
Definition term265 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1))) \/ (Peano.le x0 x1)).
Definition term48 (x0 : nat) := Peano.le (Nat.add x0 x0).
Definition term262 (x0 : nat) (x1 : nat) := False \/ (Peano.le x0 x1).
Definition term237 (x0 : nat) (x1 : nat) := ((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (Nat.mul (S (NUMERAL (BIT1 0))) x1)) \/ ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 x1)).
Definition term183 (x0 : nat) (x1 : nat) := ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) \/ ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 x1)).
Definition term307 := ~ (Coq.Arith.PeanoNat.Nat.Even (NUMERAL (BIT1 0))).
Definition term249 := S (Nat.add 0 0).
Definition term261 (x0 : nat) := @eq Prop (x0 = 0).
Definition term71 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (Nat.add x0 x0) (S (Nat.add x1 x1))).
Definition term3 := fun y0 : nat => True.
Definition term289 (x0 : nat) := forall y0 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term311 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 x1).
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term263 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term219 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1))) \/ (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 x1))).
Definition term138 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 x1))).
Definition term228 := and (~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))).
Definition term227 := and (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))).
Definition term123 := NUMERAL (BIT0 (BIT1 0)).
Definition term40 (x0 : nat) := @eq nat (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term2 := fun y0 : nat => Peano.le 0 (Nat.add y0 y0).
Definition term85 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.add x0 x0)) (Nat.add x1 x1).
Definition term292 := and (forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))) = ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term270 := and (forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)).
Definition term235 := and (forall y0 : nat, forall y1 : nat, ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1)).
Definition term224 := and (forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)).
Definition term211 := and (forall y0 : nat, forall y1 : nat, (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)).
Definition term182 := and (forall y0 : nat, forall y1 : nat, ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1)).
Definition term163 := and (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)).
Definition term143 := and (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)).
Definition term136 := and (forall y0 : nat, forall y1 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)).
Definition term98 := and (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)).
Definition term97 := and (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)).
Definition term82 := and (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1)).
Definition term81 := and (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)).
Definition term63 := and (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.le y0 y1)).
Definition term62 := and (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)).
Definition term248 := Nat.add (BIT1 0) (BIT1 0).
Definition term65 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term309 := Coq.Arith.PeanoNat.Nat.Even (S (Nat.add 0 0)).
Definition term43 := fun y0 : nat => ~ (Peano.le (S (Nat.add y0 y0)) 0).
Definition term296 (x0 : nat) (x1 : nat) := False \/ ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term255 := S (Nat.add 0 (S 0)).
Definition term256 := Nat.add 0 (S 0).
Definition term293 := (forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))) = ((y0 = y1) \/ (Peano.lt y0 y1))) /\ True.
Definition term44 := fun y0 : nat => ~ ((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = 0).
Definition term302 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Even x1).
Definition term225 := ~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term84 (x0 : nat) := Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term236 (x0 : nat) (x1 : nat) := or ((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (Nat.mul (S (NUMERAL (BIT1 0))) x1)).
Definition term144 (x0 : nat) (x1 : nat) := or ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term103 (x0 : nat) (x1 : nat) := ((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term174 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term247 := BIT0 (BIT1 0).
Definition term164 (x0 : nat) (x1 : nat) := ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) \/ (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term156 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term317 (x0 : nat) (x1 : nat) := ((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1))) -> False.
Definition term52 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (Nat.add x0 x0) (Nat.add x1 x1)).
Definition term257 := S (S 0).
Definition term158 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term51 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term7 (x0 : Prop) := forall y0 : nat, x0.
Definition term105 (x0 : nat) (x1 : nat) := @eq Prop (((S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term19 := (forall y0 : nat, ~ (Peano.le (S (Nat.add y0 y0)) 0)) /\ ((forall y0 : nat, Peano.le 0 (Nat.add y0 y0)) /\ ((forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))))))).
Definition term303 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even (S (NUMERAL (BIT1 0)))) \/ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term201 := forall y0 : nat, (((S (NUMERAL (BIT1 0))) = 0) \/ (y0 = 0)) = (y0 = 0).
Definition term126 := forall y0 : nat, (((NUMERAL (BIT0 (BIT1 0))) = 0) \/ (y0 = 0)) = (y0 = 0).
Definition term252 := Nat.add (S 0) (S 0).
Definition term226 := ~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0)).
Definition term314 (x0 : nat) := True \/ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term26 (x0 : nat) := Peano.le (Nat.add x0 x0) 0.
Definition term175 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 x2).
Definition term295 (x0 : nat) (x1 : nat) := (~ ((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1)))) -> ((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) x1))) = False.
Definition term206 (x0 : nat) (x1 : nat) := @eq Prop (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 x1)).
Definition term131 (x0 : nat) (x1 : nat) := @eq Prop (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 x1)).
Definition term100 (x0 : nat) (x1 : nat) := ((S (Nat.add x0 x0)) = (S (Nat.add x1 x1))) \/ (Peano.le (S (Nat.add x0 x0)) (Nat.add x1 x1)).
Definition term301 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.mul x0 x1).
Definition term246 := (forall y0 : nat, (((S (NUMERAL (BIT1 0))) = 0) \/ (y0 = 0)) = (y0 = 0)) /\ ((forall y0 : nat, forall y1 : nat, (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (Nat.mul (S (NUMERAL (BIT1 0))) y1)) \/ ((~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1))))).
Definition term192 := (forall y0 : nat, (((NUMERAL (BIT0 (BIT1 0))) = 0) \/ (y0 = 0)) = (y0 = 0)) /\ ((forall y0 : nat, forall y1 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ ((~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt y0 y1))) = (Peano.le y0 y1))))).
Definition term173 := (forall y0 : nat, (((NUMERAL (BIT0 (BIT1 0))) = 0) \/ (y0 = 0)) = (y0 = 0)) /\ ((forall y0 : nat, forall y1 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1))))).
Definition term155 := (forall y0 : nat, (((NUMERAL (BIT0 (BIT1 0))) = 0) \/ (y0 = 0)) = (y0 = 0)) /\ ((forall y0 : nat, forall y1 : nat, (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) \/ (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le y0 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (((Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Peano.le y0 y1))))).
Definition term15 := (forall y0 : nat, Peano.le 0 (S (Nat.add y0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (Nat.add y1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Peano.le y0 y1))))).
Definition term64 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term279 (x0 : nat) := fun y0 : nat => ((x0 = y0) \/ (Peano.lt x0 y0)) = (Peano.le x0 y0).
Definition term266 (x0 : nat) := fun y0 : nat => (((Nat.mul (S (NUMERAL (BIT1 0))) x0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y0))) \/ (Peano.le x0 y0)) = (Peano.le x0 y0).
Definition term207 (x0 : nat) := fun y0 : nat => (((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le x0 y0).
Definition term132 (x0 : nat) := fun y0 : nat => (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le x0 y0).
Definition term55 (x0 : nat) := fun y0 : nat => (Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (Peano.le x0 y0).
Definition term54 (x0 : nat) := fun y0 : nat => (Peano.le (Nat.add x0 x0) (Nat.add y0 y0)) = (Peano.le x0 y0).
Definition term31 (x0 : nat) := @eq Prop ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = 0).
Definition term145 (x0 : nat) (x1 : nat) := ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) \/ (Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term299 (x0 : nat) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even (Nat.mul (S (NUMERAL (BIT1 0))) x0)) = (Coq.Arith.PeanoNat.Nat.Even (S (Nat.mul (S (NUMERAL (BIT1 0))) x1)))) -> False.
Definition term253 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term229 (x0 : nat) (x1 : nat) := (~ ((S (NUMERAL (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 x1).
Definition term176 (x0 : nat) (x1 : nat) := (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 x1).
Definition term276 (x0 : nat) (x1 : nat) := or (x0 = x1).
Definition term316 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even (Nat.mul (S (NUMERAL (BIT1 0))) x0)).
Definition term290 := fun y0 : nat => forall y1 : nat, (((Nat.mul (S (NUMERAL (BIT1 0))) y0) = (S (Nat.mul (S (NUMERAL (BIT1 0))) y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term259 := NUMERAL (BIT1 0).
Definition term312 := Coq.Arith.PeanoNat.Nat.Even (Nat.add 0 0).
Definition term271 (x0 : nat) (x1 : nat) := True /\ (Peano.lt x0 x1).
Definition term274 (x0 : nat) (x1 : nat) := ((S (NUMERAL (BIT1 0))) = (NUMERAL 0)) \/ (x0 = x1).
