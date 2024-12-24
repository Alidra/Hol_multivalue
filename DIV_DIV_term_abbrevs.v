Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term38 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term116 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0).
Definition term179 := (~ False) -> False.
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => (Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) x2).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) x2.
Definition term63 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le y0 x0) \/ (~ (Peano.le y0 x1)).
Definition term129 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) \/ (~ (x0 = y0))) /\ ((Peano.le y0 x0) \/ (~ (x0 = y0))).
Definition term108 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0).
Definition term85 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0).
Definition term47 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.le y1 x0) \/ (~ (Peano.le y1 x1))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 x0)) \/ (Peano.le y1 x1)) y0).
Definition term197 := @eq nat (NUMERAL 0).
Definition term199 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term143 (x0 : Prop) := ~ (~ x0).
Definition term76 (x0 : nat) (x1 : nat) := (~ ((Peano.le x0 x1) /\ (Peano.le x1 x0))) \/ (x0 = x1).
Definition term218 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y2 (Nat.div y1 y0)) = (Peano.le (Nat.mul y0 y2) y1)) x0.
Definition term207 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2)) x0.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) \/ (~ (Peano.le x1 x2))) /\ ((~ (Peano.le x1 x0)) \/ (Peano.le x1 x2)).
Definition term148 (x0 : nat) := (x0 = x0) -> Peano.le x0 x0.
Definition term28 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.le x0 x1).
Definition term94 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0).
Definition term58 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le y1 x0) \/ (~ (Peano.le y1 x1))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 x0)) \/ (Peano.le y1 x1)) y0).
Definition term11 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False.
Definition term245 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term13 (x0 : nat) (x1 : nat) := (((~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False.
Definition term198 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div x0 (Nat.mul x1 x2).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term89 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) x1.
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) \/ (~ (Peano.le x1 x2)).
Definition term139 (x0 : nat) := ~ (x0 = x0).
Definition term235 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (Peano.le x0 (Nat.div (Nat.div x1 x2) x3)).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term109 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0).
Definition term86 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0).
Definition term48 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.le y1 x0) \/ (~ (Peano.le y1 x1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le y1 x0)) \/ (Peano.le y1 x1)) y0).
Definition term127 := (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y0 : nat, forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)).
Definition term82 (x0 : nat) := forall y0 : nat, (((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0)).
Definition term37 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) /\ ((~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)).
Definition term174 (x0 : nat) (x1 : nat) := imp (~ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1)))).
Definition term104 (x0 : nat) := forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0).
Definition term71 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) /\ (forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1))) /\ (~ (x0 = x1)).
Definition term88 (x0 : nat) := fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0).
Definition term202 (x0 : nat) := (fun y0 : nat => (Nat.div (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term200 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term29 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term30 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term103 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0.
Definition term98 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term67 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le y1 x0)) \/ (Peano.le y1 x1)) y0.
Definition term62 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le y1 x0) \/ (~ (Peano.le y1 x1))) y0.
Definition term211 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0)) x2.
Definition term194 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.div x0 x1) x2.
Definition term141 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term45 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term81 (x0 : nat) := fun y0 : nat => (((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0)).
Definition term106 := fun y0 : nat => (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)).
Definition term16 := ~ (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)).
Definition term134 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.le x0 y0) \/ (~ (x0 = y0))) /\ ((Peano.le y0 x0) \/ (~ (x0 = y0)))) x1.
Definition term178 (x0 : nat) (x1 : nat) := (x0 = x1) -> False.
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)) x2.
Definition term74 (x0 : nat) (x1 : nat) := or (~ ((Peano.le x1 x0) /\ (Peano.le x0 x1))).
Definition term156 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term177 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) -> x0 = x1.
Definition term33 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1).
Definition term140 (x0 : Prop) := (~ x0) -> x0.
Definition term203 (x0 : nat) := Nat.div (NUMERAL 0) x0.
Definition term137 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (~ (x0 = x1)).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) x2) /\ ((fun y0 : nat => (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)) x2).
Definition term169 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term229 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x0 x1) (Nat.div x2 x3).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Peano.le x1 x0) \/ (~ (Peano.le x1 x2))).
Definition term150 (x0 : nat) := ~ (Peano.le x0 x0).
Definition term138 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term147 (x0 : nat) (x1 : nat) := (x1 = x0) -> Peano.le x0 x1.
Definition term159 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term79 (x0 : nat) (x1 : nat) := (((Peano.le x0 x1) /\ (Peano.le x1 x0)) \/ (~ (x0 = x1))) /\ ((~ ((Peano.le x0 x1) /\ (Peano.le x1 x0))) \/ (x0 = x1)).
Definition term32 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le y0 x0) = (Peano.le y0 x1).
Definition term118 := @eq Prop (forall y0 : nat, (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1))).
Definition term117 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0)).
Definition term96 (x0 : nat) := @eq Prop (forall y0 : nat, (((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0))).
Definition term95 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0)).
Definition term60 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) /\ ((~ (Peano.le y0 x0)) \/ (Peano.le y0 x1))).
Definition term59 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.le y1 x0) \/ (~ (Peano.le y1 x1))) y0) /\ ((fun y1 : nat => (~ (Peano.le y1 x0)) \/ (Peano.le y1 x1)) y0)).
Definition term210 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term36 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) /\ ((~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 x2) (Nat.div x3 x0)) = (Peano.le (Nat.mul x0 (Nat.mul x1 x2)) x3).
Definition term233 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (Nat.mul x0 x1) x2).
Definition term149 (x0 : nat) := (~ (Peano.le x0 x0)) -> Peano.le x0 x0.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term215 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0))).
Definition term220 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0)) x1.
Definition term209 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1)) x1.
Definition term42 (x0 : nat) (x1 : nat) := (forall y0 : nat, ((Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) /\ ((~ (Peano.le y0 x0)) \/ (Peano.le y0 x1))) /\ (~ (x0 = x1)).
Definition term41 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) /\ (~ (x0 = x1)).
Definition term186 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term166 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = x0) \/ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1)))).
Definition term193 (x0 : nat) (x1 : nat) := Nat.div (Nat.div x0 x1).
Definition term216 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL 0)))) x1.
Definition term111 := fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1).
Definition term31 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term21 (x0 : nat) := fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) = (Peano.le y1 x0)) -> y0 = x0)) -> ~ (forall y1 : nat, forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)).
Definition term196 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.div (Nat.div x0 x1) x2).
Definition term241 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le y0 (Nat.div (Nat.div x0 x1) x2)) = (Peano.le y0 (Nat.div x0 (Nat.mul x1 x2))).
Definition term73 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1)).
Definition term142 (x0 : nat) (x1 : nat) := (~ (~ (x1 = x0))) -> Peano.le x0 x1.
Definition term161 (x0 : nat) (x1 : nat) := (x1 = x0) \/ (~ (Peano.le x0 x1)).
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x1 (Nat.div (Nat.div x2 x3) x0)) = (Peano.le (Nat.mul x0 x1) (Nat.div x2 x3)).
Definition term70 (x0 : nat) (x1 : nat) := and ((forall y0 : nat, (Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) /\ (forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1))).
Definition term136 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term97 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term61 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le y1 x0) \/ (~ (Peano.le y1 x1))) y0.
Definition term206 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, (Peano.le y0 (Nat.div (Nat.div x0 x1) x2)) = (Peano.le y0 (Nat.div x0 (Nat.mul x1 x2)))) -> (Nat.div (Nat.div x0 x1) x2) = (Nat.div x0 (Nat.mul x1 x2)).
Definition term191 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term187 (x0 : nat) := (fun y0 : nat => (Nat.div y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term164 (x0 : nat) (x1 : nat) := (x1 = x0) \/ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term15 := (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False.
Definition term10 (x0 : nat) (x1 : nat) := ~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1).
Definition term68 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1).
Definition term34 (x0 : nat) (x1 : nat) := imp (forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)).
Definition term101 (x0 : nat) := and (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))).
Definition term65 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (Peano.le y0 x0) \/ (~ (Peano.le y0 x1))).
Definition term40 (x0 : nat) (x1 : nat) := and (forall y0 : nat, ((Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) /\ ((~ (Peano.le y0 x0)) \/ (Peano.le y0 x1))).
Definition term39 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)).
Definition term146 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term213 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term238 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term168 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term49 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le y0 x0) \/ (~ (Peano.le y0 x1)).
Definition term249 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.div (Nat.div y0 y1) y2) = (Nat.div y0 (Nat.mul y1 y2)).
Definition term248 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.div (Nat.div x0 y0) y1) = (Nat.div x0 (Nat.mul y0 y1)).
Definition term219 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0).
Definition term208 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term132 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) \/ (~ (y0 = y1))) /\ ((Peano.le y1 y0) \/ (~ (y0 = y1))).
Definition term126 := forall y0 : nat, forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1).
Definition term121 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1)).
Definition term84 := forall y0 : nat, forall y1 : nat, (((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)).
Definition term27 := forall y0 : nat, forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) = (Peano.le y2 y0)) -> y1 = y0)) -> ~ (forall y2 : nat, forall y3 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y2)) = (y2 = y3)).
Definition term26 := forall y0 : nat, forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) = (Peano.le y2 y0)) -> y1 = y0)) -> (forall y2 : nat, forall y3 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y2)) = (y2 = y3)) -> False.
Definition term17 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term163 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ ((x1 = x0) \/ (~ (Peano.le x0 x1))).
Definition term217 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL 0)).
Definition term115 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) x0) /\ ((fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)) x0).
Definition term185 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term80 (x0 : nat) (x1 : nat) := (((Peano.le x0 x1) /\ (Peano.le x1 x0)) \/ (~ (x0 = x1))) /\ (((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x0))) \/ (x0 = x1)).
Definition term176 (x0 : nat) (x1 : nat) := ((Peano.le x0 x1) /\ (Peano.le x1 x0)) -> x0 = x1.
Definition term78 (x0 : nat) (x1 : nat) := and (((Peano.le x0 x1) /\ (Peano.le x1 x0)) \/ (~ (x0 = x1))).
Definition term244 := forall y0 : nat, True.
Definition term99 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term232 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.mul x1 x2)).
Definition term72 (x0 : nat) (x1 : nat) := ~ ((Peano.le x1 x0) /\ (Peano.le x0 x1)).
Definition term222 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1)) x2.
Definition term204 := Nat.div (NUMERAL 0).
Definition term225 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x1) x2.
Definition term242 := fun y0 : nat => True.
Definition term75 (x0 : nat) (x1 : nat) := or ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term183 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1) -> (forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1.
Definition term181 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) = (Peano.le y1 x0)) -> y0 = x0)) -> (forall y1 : nat, forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) -> False) x1.
Definition term182 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1) -> x0 = x1.
Definition term93 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) x1) /\ ((fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0)) x1).
Definition term46 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term22 (x0 : nat) := forall y0 : nat, (~ ((forall y1 : nat, (Peano.le y1 y0) = (Peano.le y1 x0)) -> y0 = x0)) -> (forall y1 : nat, forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) -> False.
Definition term160 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (x0 = x1).
Definition term135 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) \/ ((~ (Peano.le x1 x0)) \/ (x0 = x1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term172 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term162 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term18 (x0 : nat) (x1 : nat) := imp (~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)).
Definition term105 (x0 : nat) := (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) /\ (forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0)).
Definition term69 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.le y0 x0) \/ (~ (Peano.le y0 x1))) /\ (forall y0 : nat, (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1)).
Definition term123 := and (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))).
Definition term124 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0.
Definition term119 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ (Peano.le x1 x2)).
Definition term231 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x0 (Nat.mul x1 x2)) x3.
Definition term175 (x0 : nat) (x1 : nat) := imp ((Peano.le x1 x0) /\ (Peano.le x0 x1)).
Definition term214 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL 0)))) x0.
Definition term180 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) = (Peano.le y2 y0)) -> y1 = y0)) -> (forall y2 : nat, forall y3 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y2)) = (y2 = y3)) -> False) x0.
Definition term133 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) \/ (~ (y0 = y1))) /\ ((Peano.le y1 y0) \/ (~ (y0 = y1)))) x0.
Definition term114 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)) x0.
Definition term112 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) x0.
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x1 (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 x1) x2).
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.div x1 x2).
Definition term195 (x0 : nat) (x1 : nat) := Nat.div (Nat.div x0 x1) (NUMERAL 0).
Definition term190 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term12 (x0 : nat) (x1 : nat) := ((~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False.
Definition term154 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x1 x0) \/ (~ (Peano.le x1 x2))).
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term167 (x0 : nat) (x1 : nat) := (~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x0)))) -> x0 = x1.
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le y0 (Nat.div (Nat.div x0 x1) x2)) = (Peano.le y0 (Nat.div x0 (Nat.mul x1 x2))).
Definition term192 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term170 (x0 : nat) (x1 : nat) := ~ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term50 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.le y0 x0)) \/ (Peano.le y0 x1).
Definition term90 (x0 : nat) (x1 : nat) := ((Peano.le x0 x1) /\ (Peano.le x1 x0)) \/ (~ (x0 = x1)).
Definition term102 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0.
Definition term66 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le y1 x0)) \/ (Peano.le y1 x1)) y0.
Definition term77 (x0 : nat) (x1 : nat) := ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x0))) \/ (x0 = x1).
Definition term122 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0).
Definition term100 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0).
Definition term64 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.le y1 x0) \/ (~ (Peano.le y1 x1))) y0).
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((Nat.mul x0 x1) = (NUMERAL 0))) -> (Peano.le x2 (Nat.div x3 (Nat.mul x0 x1))) = (Peano.le (Nat.mul (Nat.mul x0 x1) x2) x3).
Definition term113 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) x0).
Definition term130 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) \/ (~ (x0 = y0))) /\ ((Peano.le y0 x0) \/ (~ (x0 = y0))).
Definition term226 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term19 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> ~ (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)).
Definition term128 (x0 : nat) (x1 : nat) := ((Peano.le x0 x1) \/ (~ (x0 = x1))) /\ ((Peano.le x1 x0) \/ (~ (x0 = x1))).
Definition term246 (x0 : Prop) := forall y0 : nat, x0.
Definition term165 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.le x0 x1)) \/ ((~ (Peano.le x1 x0)) \/ (x0 = x1))).
Definition term247 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.div (Nat.div x0 x1) y0) = (Nat.div x0 (Nat.mul x1 y0)).
Definition term110 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1)).
Definition term25 := fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) = (Peano.le y2 y0)) -> y1 = y0)) -> ~ (forall y2 : nat, forall y3 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y2)) = (y2 = y3)).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term239 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x0 x1) = (NUMERAL 0)).
Definition term107 := forall y0 : nat, (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)).
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul (Nat.mul x0 x1) x2) x3.
Definition term205 := Nat.mul (NUMERAL 0).
Definition term9 (x0 : nat) (x1 : nat) := (~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> False.
Definition term201 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term91 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) x1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term236 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (Peano.le (Nat.mul (Nat.mul x0 x1) x2) x3).
Definition term158 (x0 : nat) (x1 : nat) := (Peano.le x0 x0) -> Peano.le x0 x1.
Definition term23 (x0 : nat) := forall y0 : nat, (~ ((forall y1 : nat, (Peano.le y1 y0) = (Peano.le y1 x0)) -> y0 = x0)) -> ~ (forall y1 : nat, forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le x0 (Nat.div (Nat.div x1 x2) x3).
Definition term92 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0)) x1.
Definition term144 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term14 (x0 : nat) (x1 : nat) := (((~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False) -> ((~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False) -> (~ ((forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> False.
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ (Peano.le x1 x2).
Definition term221 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1).
Definition term87 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0)).
Definition term188 (x0 : nat) := Nat.div x0 (NUMERAL 0).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> Peano.le x1 x2.
Definition term125 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0.
Definition term120 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term189 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term24 := fun y0 : nat => forall y1 : nat, (~ ((forall y2 : nat, (Peano.le y2 y1) = (Peano.le y2 y0)) -> y1 = y0)) -> (forall y2 : nat, forall y3 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y2)) = (y2 = y3)) -> False.
Definition term8 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Peano.le y0 x0) = (Peano.le y0 x1)) -> x0 = x1.
Definition term171 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x1 x0))) /\ (~ (~ (Peano.le x0 x1))).
Definition term184 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term240 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le x0 (Nat.div x1 (Nat.mul x2 x3)).
Definition term131 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) \/ (~ (y0 = y1))) /\ ((Peano.le y1 y0) \/ (~ (y0 = y1))).
Definition term83 := fun y0 : nat => forall y1 : nat, (((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)).
Definition term173 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term20 (x0 : nat) := fun y0 : nat => (~ ((forall y1 : nat, (Peano.le y1 y0) = (Peano.le y1 x0)) -> y0 = x0)) -> (forall y1 : nat, forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) = (y1 = y2)) -> False.
Definition term155 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
Definition term145 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x0))) -> Peano.le x1 x2.
