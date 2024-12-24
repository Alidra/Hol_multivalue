Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term186 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := exists y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) y0) /\ ((~ (x4 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4))).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term115 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (~ (nadd_le y0 y1)) -> forall y2 : nat, exists y3 : nat, (~ (y3 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd y1 y3) y2) (dest_nadd y0 y3))) x0.
Definition term181 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := exists y0 : nat, (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0))).
Definition term192 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x4 y0) (Nat.add x2 x3)) (dest_nadd x1 y0))) x0) /\ ((~ (x5 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5))).
Definition term152 (x0 : nadd) (x1 : nadd) (x2 : nat) := and ((fun y0 : nat => exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1))) x2).
Definition term236 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.add (Nat.mul x3 (dest_nadd x0 x1)) (Nat.add (Nat.mul x3 x2) (Nat.mul x3 x4))).
Definition term194 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) y0) /\ ((~ (x4 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4))).
Definition term156 (x0 : nadd) (x1 : nadd) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y2) y1) (dest_nadd x0 y2))) y0) /\ ((fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y2) y1) (dest_nadd x1 y2))) y0).
Definition term249 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := and (Peano.le (Nat.mul x1 (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.add (Nat.mul x1 x3) (Nat.mul x2 x3)))).
Definition term253 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x2 (dest_nadd x0 x1)) (Nat.add (Nat.mul x1 (dest_nadd x0 x2)) (Nat.mul (Nat.add x1 x2) x3)).
Definition term222 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := and (Peano.lt (Nat.mul x3 (Nat.add (dest_nadd x0 x5) (Nat.add x1 x2))) (Nat.mul x3 (dest_nadd x4 x5))).
Definition term151 (x0 : nadd) (x1 : nadd) := @eq Prop ((forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y1) y0) (dest_nadd x0 y1))) /\ (forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)))).
Definition term150 (x0 : nadd) (x1 : nadd) := @eq Prop ((forall y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y2) y1) (dest_nadd x0 y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y2) y1) (dest_nadd x1 y2))) y0)).
Definition term277 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) \/ (nadd_le y0 x0).
Definition term142 (x0 : nadd) (x1 : nadd) := forall y0 : nat, ((fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y2) y1) (dest_nadd x0 y2))) y0) /\ ((fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y2) y1) (dest_nadd x1 y2))) y0).
Definition term124 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term240 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.add (Nat.add (Nat.mul x4 (dest_nadd x0 x3)) (Nat.add (Nat.mul x3 x1) (Nat.mul x4 x1))) (Nat.add (Nat.mul x3 (dest_nadd x2 x4)) (Nat.add (Nat.mul x3 x5) (Nat.mul x4 x5))).
Definition term237 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.add (Nat.add (Nat.mul x2 (dest_nadd x0 x4)) (Nat.add (Nat.mul x2 x3) (Nat.mul x2 x5))) (Nat.add (Nat.mul x4 (dest_nadd x1 x2)) (Nat.add (Nat.mul x4 x3) (Nat.mul x4 x5))).
Definition term233 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.add (Nat.mul x0 (dest_nadd x1 x2)).
Definition term133 (x0 : nadd) (x1 : nadd) := ~ ((~ (nadd_le x1 x0)) /\ (~ (nadd_le x0 x1))).
Definition term201 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := (((~ (x0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x4 x0) (Nat.add x2 x3)) (dest_nadd x1 x0))) /\ ((~ (x5 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5)))) -> (~ ((x5 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x4 x0) (Nat.add x2 x3)) (dest_nadd x1 x0))))) /\ (~ ((x0 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5))))).
Definition term126 (x0 : Prop) := ~ (~ x0).
Definition term89 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)) = (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term63 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term52 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2)) = (Nat.mul (Nat.add y0 y1) y2)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (dist (@pair nat nat y0 y1)) y2) = ((Peano.le y0 (Nat.add y1 y2)) /\ (Peano.le y1 (Nat.add y0 y2)))) x0.
Definition term106 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (x0 /\ (exists y1 : a0, y0 y1)) = (exists y1 : a0, x0 /\ (y0 y1)).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term135 (x0 : nadd) (x1 : nadd) := forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)).
Definition term244 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x1 (dest_nadd x0 x2)) (Nat.add (Nat.mul x1 x3) (Nat.mul x2 x3)).
Definition term197 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := fun y0 : nat => exists y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0))).
Definition term143 (x0 : nadd) (x1 : nadd) := fun y0 : nat => exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)).
Definition term95 (x0 : Prop) := (fun y0 : Prop => y0 -> False) x0.
Definition term39 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term254 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := (Peano.le (Nat.mul x3 (dest_nadd x0 x4)) (Nat.add (Nat.mul x4 (dest_nadd x0 x3)) (Nat.add (Nat.mul x3 x1) (Nat.mul x4 x1)))) /\ (Peano.le (Nat.mul x4 (dest_nadd x2 x3)) (Nat.add (Nat.mul x3 (dest_nadd x2 x4)) (Nat.add (Nat.mul x3 x5) (Nat.mul x4 x5)))).
Definition term210 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := (x0 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5))).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nadd) (x5 : nat) := ~ (Peano.lt (Nat.add (Nat.mul x5 (Nat.add (dest_nadd x4 x3) (Nat.add x0 x1))) (Nat.mul x3 (Nat.add (dest_nadd x2 x5) (Nat.add x0 x1)))) (Nat.add (Nat.mul x5 (dest_nadd x2 x3)) (Nat.mul x3 (dest_nadd x4 x5)))).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term191 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := and ((~ (x4 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4))).
Definition term162 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0)))) -> False.
Definition term212 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (Nat.add (dest_nadd x2 x3) (Nat.add x4 x5))).
Definition term206 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := ~ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4)).
Definition term278 := forall y0 : nadd, forall y1 : nadd, (nadd_le y0 y1) \/ (nadd_le y1 y0).
Definition term109 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term77 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term141 (x0 : nadd) (x1 : nadd) := (forall y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y2) y1) (dest_nadd x0 y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y2) y1) (dest_nadd x1 y2))) y0).
Definition term136 (x0 : nadd) (x1 : nadd) := (forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y1) y0) (dest_nadd x0 y1))) /\ (forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1))).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.add x0 x1) (Nat.add x2 (Nat.add x3 x4)).
Definition term250 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := and (Peano.le (Nat.mul x1 (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.mul (Nat.add x1 x2) x3))).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.add x0 (Nat.add (Nat.add x1 x2) (Nat.add x3 (Nat.add x4 x5))).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (dist (@pair nat nat x1 x0)) y0) = ((Peano.le x1 (Nat.add x0 y0)) /\ (Peano.le x0 (Nat.add x1 y0)))) x2.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)) = (Nat.mul (Nat.add x0 x1) y0)) x2.
Definition term230 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := Nat.add (Nat.mul x3 (dest_nadd x0 x1)) (Nat.mul x1 (dest_nadd x2 x3)).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x2 x3)).
Definition term179 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := fun y0 : nat => (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) /\ ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) (Nat.add x1 x2)) (dest_nadd x3 y1))) y0).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x2 (Nat.add x3 x4))).
Definition term216 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := and (~ (Peano.le (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (Nat.add (dest_nadd x2 x3) (Nat.add x4 x5))))).
Definition term140 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term159 (x0 : nadd) (x1 : nadd) := ~ (forall y0 : nat, (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y1) y0) (dest_nadd x0 y1))) /\ (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)))).
Definition term127 (x0 : nadd) (x1 : nadd) := (nadd_le x1 x0) \/ (nadd_le x0 x1).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1))) x1.
Definition term247 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x1 (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.add (Nat.mul x1 x3) (Nat.mul x2 x3))).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term108 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term121 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term261 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul x2 (dest_nadd x0 x3)) (Nat.add (Nat.mul x3 (dest_nadd x0 x2)) (Nat.mul x1 (Nat.add x2 x3)))) /\ (Peano.le (Nat.mul x3 (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x1 (Nat.add x2 x3)))).
Definition term224 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := ~ ((Peano.lt (Nat.mul x5 (Nat.add (dest_nadd x4 x3) (Nat.add x1 x2))) (Nat.mul x5 (dest_nadd x0 x3))) /\ (Peano.lt (Nat.mul x3 (Nat.add (dest_nadd x0 x5) (Nat.add x1 x2))) (Nat.mul x3 (dest_nadd x4 x5)))).
Definition term122 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term107 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 /\ (exists y1 : a0, y0 y1)) = (exists y1 : a0, x0 /\ (y0 y1))) x1.
Definition term203 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := (~ ((x5 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x4 x0) (Nat.add x2 x3)) (dest_nadd x1 x0))))) /\ (~ ((x0 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5))))).
Definition term214 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := ~ (Peano.le (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (Nat.add (dest_nadd x2 x3) (Nat.add x4 x5)))).
Definition term270 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x2 (dest_nadd x0 y0)) (Nat.add (Nat.mul y0 (dest_nadd x0 x2)) (Nat.mul x1 (Nat.add x2 y0)))) /\ (Peano.le (Nat.mul y0 (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul x1 (Nat.add x2 y0))))) x3.
Definition term207 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) (Nat.add x3 x4)).
Definition term130 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term169 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0)).
Definition term187 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := and (exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) (Nat.add x1 x2)) (dest_nadd x3 y1))) y0).
Definition term119 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term258 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x1 (Nat.add x2 x3)).
Definition term15 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)) = (Nat.mul (Nat.add x0 x1) y0).
Definition term221 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (dest_nadd x1 x2).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term120 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term185 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := (exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) y0) /\ ((~ (x4 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4))).
Definition term208 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (dest_nadd x0 x1) (Nat.add x2 x3).
Definition term241 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.add (Nat.mul x3 (dest_nadd x0 x4)) (Nat.mul x4 (dest_nadd x2 x3))) (Nat.add (Nat.add (Nat.mul x4 (dest_nadd x0 x3)) (Nat.add (Nat.mul x3 x1) (Nat.mul x4 x1))) (Nat.add (Nat.mul x3 (dest_nadd x2 x4)) (Nat.add (Nat.mul x3 x5) (Nat.mul x4 x5)))).
Definition term239 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.add (Nat.mul x2 (dest_nadd x1 x4)) (Nat.mul x4 (dest_nadd x0 x2))) (Nat.add (Nat.add (Nat.mul x2 (dest_nadd x0 x4)) (Nat.add (Nat.mul x2 x3) (Nat.mul x2 x5))) (Nat.add (Nat.mul x4 (dest_nadd x1 x2)) (Nat.add (Nat.mul x4 x3) (Nat.mul x4 x5)))).
Definition term146 (x0 : nadd) (x1 : nadd) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y2) y1) (dest_nadd x1 y2))) y0.
Definition term227 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nadd) (x5 : nat) := (Peano.lt (Nat.add (Nat.mul x5 (Nat.add (dest_nadd x4 x3) (Nat.add x0 x1))) (Nat.mul x3 (Nat.add (dest_nadd x2 x5) (Nat.add x0 x1)))) (Nat.add (Nat.mul x5 (dest_nadd x2 x3)) (Nat.mul x3 (dest_nadd x4 x5)))) -> False.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((exists y1 : a0, x0 y1) /\ y0) = (exists y1 : a0, (x0 y1) /\ y0).
Definition term144 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1))) x2.
Definition term190 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := and ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0))) x4).
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term54 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)) = (Nat.mul (Nat.add x0 y0) y1)) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (dist (@pair nat nat x0 y0)) y1) = ((Peano.le x0 (Nat.add y0 y1)) /\ (Peano.le y0 (Nat.add x0 y1)))) x1.
Definition term275 (x0 : nadd) (x1 : nadd) := ((~ (nadd_le x1 x0)) /\ (~ (nadd_le x0 x1))) -> False.
Definition term17 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)) = (Nat.mul (Nat.add x0 y0) y1).
Definition term105 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (y0 /\ (exists y2 : a0, y1 y2)) = (exists y2 : a0, y0 /\ (y1 y2))) x0.
Definition term257 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x2 (dest_nadd x0 x3)) (Nat.add (Nat.mul x3 (dest_nadd x0 x2)) (Nat.mul x1 (Nat.add x2 x3))).
Definition term92 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := ((~ x0) /\ x1) /\ ((~ x2) /\ x3).
Definition term238 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := Peano.le (Nat.add (Nat.mul x3 (dest_nadd x0 x1)) (Nat.mul x1 (dest_nadd x2 x3))).
Definition term229 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.add (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x1 (dest_nadd x0 x3))) (Nat.add (Nat.mul x3 (Nat.add (dest_nadd x0 x1) (Nat.add x4 x5))) (Nat.mul x1 (Nat.add (dest_nadd x2 x3) (Nat.add x4 x5)))).
Definition term219 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := Peano.lt (Nat.mul x3 (Nat.add (dest_nadd x0 x5) (Nat.add x1 x2))) (Nat.mul x3 (dest_nadd x4 x5)).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (dist (@pair nat nat x1 x0)) y0) = ((Peano.le x1 (Nat.add x0 y0)) /\ (Peano.le x0 (Nat.add x1 y0))).
Definition term165 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term215 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := and (~ ((x0 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5))))).
Definition term170 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0))) x4.
Definition term74 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term168 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0)).
Definition term145 (x0 : nadd) (x1 : nat) (x2 : nadd) := exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) x1) (dest_nadd x2 y0)).
Definition term164 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term176 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := @eq Prop ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0)))).
Definition term175 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := @eq Prop ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ (exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) (Nat.add x1 x2)) (dest_nadd x3 y1))) y0)).
Definition term200 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((~ x2) /\ x1) /\ ((~ x0) /\ x3)) -> (~ (x0 \/ (~ x1))) /\ (~ (x2 \/ (~ x3))).
Definition term273 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := (exists y0 : nat, exists y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0)))) -> False.
Definition term166 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ (exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) (Nat.add x1 x2)) (dest_nadd x3 y1))) y0).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x2 (Nat.add x3 (Nat.add x4 x5)))).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term264 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term209 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term96 (x0 : Prop) := @eq Prop (~ x0).
Definition term129 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term268 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul y0 (dest_nadd x0 y1)) (Nat.add (Nat.mul y1 (dest_nadd x0 y0)) (Nat.mul x1 (Nat.add y0 y1)))) /\ (Peano.le (Nat.mul y1 (dest_nadd x0 y0)) (Nat.add (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul x1 (Nat.add y0 y1)))).
Definition term125 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term88 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)) = (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term87 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)).
Definition term84 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term83 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term66 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term64 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term53 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term31 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1).
Definition term29 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2).
Definition term27 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3).
Definition term23 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2)) = (Nat.mul (Nat.add y0 y1) y2).
Definition term22 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2)).
Definition term19 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)) = (Nat.mul (Nat.add x0 y0) y1).
Definition term18 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (dist (@pair nat nat x0 y0)) y1) = ((Peano.le x0 (Nat.add y0 y1)) /\ (Peano.le y0 (Nat.add x0 y1))).
Definition term157 (x0 : nadd) (x1 : nadd) := fun y0 : nat => (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y1) y0) (dest_nadd x0 y1))) /\ (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1))).
Definition term243 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.add (Nat.mul x1 x3) (Nat.mul x2 x3)).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term269 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul y0 (dest_nadd x0 y1)) (Nat.add (Nat.mul y1 (dest_nadd x0 y0)) (Nat.mul x1 (Nat.add y0 y1)))) /\ (Peano.le (Nat.mul y1 (dest_nadd x0 y0)) (Nat.add (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul x1 (Nat.add y0 y1))))) x2.
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term72 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term60 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term65 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term117 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (~ (nadd_le x0 y0)) -> forall y1 : nat, exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd y0 y2) y1) (dest_nadd x0 y2))) x1.
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.lt x0 x2) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term12 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1)).
Definition term274 (x0 : nadd) (x1 : nadd) := (forall y0 : nat, (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y1) y0) (dest_nadd x0 y1))) /\ (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)))) -> False.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x0 x2) /\ (Peano.lt x1 x3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term246 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul x0 (dest_nadd x1 x2)).
Definition term178 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ ((~ (x4 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4))).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2)) = (forall y2 : a0, (y0 y2) /\ (y1 y2))) x0.
Definition term100 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((exists y2 : a0, y0 y2) /\ y1) = (exists y2 : a0, (y0 y2) /\ y1)) x0.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term80 (x0 : nat) (x1 : nat) := forall y0 : nat, ((x1 = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term79 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term55 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term242 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := ((Peano.le (Nat.mul x3 (dest_nadd x0 x4)) (Nat.add (Nat.mul x4 (dest_nadd x0 x3)) (Nat.add (Nat.mul x3 x1) (Nat.mul x4 x1)))) /\ (Peano.le (Nat.mul x4 (dest_nadd x2 x3)) (Nat.add (Nat.mul x3 (dest_nadd x2 x4)) (Nat.add (Nat.mul x3 x5) (Nat.mul x4 x5))))) -> Peano.le (Nat.add (Nat.mul x3 (dest_nadd x0 x4)) (Nat.mul x4 (dest_nadd x2 x3))) (Nat.add (Nat.add (Nat.mul x4 (dest_nadd x0 x3)) (Nat.add (Nat.mul x3 x1) (Nat.mul x4 x1))) (Nat.add (Nat.mul x3 (dest_nadd x2 x4)) (Nat.add (Nat.mul x3 x5) (Nat.mul x4 x5)))).
Definition term231 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.add (Nat.mul x3 (Nat.add (dest_nadd x0 x1) (Nat.add x4 x5))) (Nat.mul x1 (Nat.add (dest_nadd x2 x3) (Nat.add x4 x5))).
Definition term189 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := @eq Prop ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ ((~ (x4 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4)))).
Definition term188 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) y0) /\ ((~ (x4 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4)))).
Definition term184 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term196 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := exists y0 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ ((~ (x4 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4))).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((x1 = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term13 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)) = (Nat.mul (Nat.add x0 x1) y0).
Definition term256 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x3 (dest_nadd x0 x2)) (Nat.mul x1 (Nat.add x2 x3)).
Definition term226 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nadd) (x5 : nat) := Peano.lt (Nat.add (Nat.mul x5 (Nat.add (dest_nadd x4 x3) (Nat.add x0 x1))) (Nat.mul x3 (Nat.add (dest_nadd x2 x5) (Nat.add x0 x1)))) (Nat.add (Nat.mul x5 (dest_nadd x2 x3)) (Nat.mul x3 (dest_nadd x4 x5))).
Definition term8 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term139 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term131 (x0 : nadd) (x1 : nadd) := ~ ((nadd_le x1 x0) \/ (nadd_le x0 x1)).
Definition term97 (x0 : Prop) (x1 : Prop) := (x0 \/ (~ x1)) -> False.
Definition term202 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4).
Definition term211 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (dest_nadd x1 x3) (Nat.add (dest_nadd x2 x3) (Nat.add x4 x5))).
Definition term173 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := exists y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) (Nat.add x1 x2)) (dest_nadd x3 y1))) y0.
Definition term204 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := ((~ ((x5 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x4 x0) (Nat.add x2 x3)) (dest_nadd x1 x0))))) /\ (~ ((x0 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5)))))) -> False.
Definition term223 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := (Peano.lt (Nat.mul x5 (Nat.add (dest_nadd x4 x3) (Nat.add x1 x2))) (Nat.mul x5 (dest_nadd x0 x3))) /\ (Peano.lt (Nat.mul x3 (Nat.add (dest_nadd x0 x5) (Nat.add x1 x2))) (Nat.mul x3 (dest_nadd x4 x5))).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := @eq nat (Nat.add (Nat.add x0 (Nat.add x1 x2)) (Nat.add x3 (Nat.add x4 x5))).
Definition term138 (x0 : nadd) (x1 : nadd) := ~ ((forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y1) y0) (dest_nadd x0 y1))) /\ (forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)))).
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term235 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.mul x0 (Nat.add (dest_nadd x1 x2) (Nat.add x3 x4))).
Definition term149 (x0 : nadd) (x1 : nadd) := and (forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1))).
Definition term154 (x0 : nadd) (x1 : nadd) (x2 : nat) := ((fun y0 : nat => exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y1) y0) (dest_nadd x0 y1))) x2) /\ ((fun y0 : nat => exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1))) x2).
Definition term62 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term183 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term232 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.mul x2 (Nat.add x3 x4)).
Definition term171 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := (~ (x4 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4)).
Definition term93 (x0 : Prop) (x1 : Prop) := x0 \/ (~ x1).
Definition term161 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0))).
Definition term155 (x0 : nadd) (x1 : nat) (x2 : nadd) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x2 y0) x1) (dest_nadd x0 y0))) /\ (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) x1) (dest_nadd x2 y0))).
Definition term71 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term59 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term218 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := ~ ((~ (Peano.le (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x3 (Nat.add (dest_nadd x0 x1) (Nat.add x4 x5))))) /\ (~ (Peano.le (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (Nat.add (dest_nadd x2 x3) (Nat.add x4 x5)))))).
Definition term205 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := ~ ((~ ((x5 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x4 x0) (Nat.add x2 x3)) (dest_nadd x1 x0))))) /\ (~ ((x0 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5)))))).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.lt x0 x2) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 y0).
Definition term99 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (~ (x0 \/ (~ x1))) /\ (~ (x2 \/ (~ x3))).
Definition term174 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := and (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0))).
Definition term153 (x0 : nadd) (x1 : nat) (x2 : nadd) := and (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) x1) (dest_nadd x2 y0))).
Definition term225 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nadd) (x5 : nat) := ((Peano.lt (Nat.mul x5 (Nat.add (dest_nadd x4 x3) (Nat.add x0 x1))) (Nat.mul x5 (dest_nadd x2 x3))) /\ (Peano.lt (Nat.mul x3 (Nat.add (dest_nadd x2 x5) (Nat.add x0 x1))) (Nat.mul x3 (dest_nadd x4 x5)))) -> Peano.lt (Nat.add (Nat.mul x5 (Nat.add (dest_nadd x4 x3) (Nat.add x0 x1))) (Nat.mul x3 (Nat.add (dest_nadd x2 x5) (Nat.add x0 x1)))) (Nat.add (Nat.mul x5 (dest_nadd x2 x3)) (Nat.mul x3 (dest_nadd x4 x5))).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.add y0 y1) (Nat.add y2 y3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term199 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := ~ (exists y0 : nat, exists y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0)))).
Definition term14 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term94 (x0 : Prop) (x1 : Prop) := (~ x0) /\ x1.
Definition term272 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := (((~ (x0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x4 x0) (Nat.add x2 x3)) (dest_nadd x1 x0))) /\ ((~ (x5 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5)))) -> False.
Definition term271 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := ((Peano.lt (Nat.mul x5 (Nat.add (dest_nadd x4 x3) (Nat.add x1 x2))) (Nat.mul x5 (dest_nadd x0 x3))) /\ (Peano.lt (Nat.mul x3 (Nat.add (dest_nadd x0 x5) (Nat.add x1 x2))) (Nat.mul x3 (dest_nadd x4 x5)))) -> False.
Definition term217 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := (~ (Peano.le (Nat.mul x3 (dest_nadd x2 x1)) (Nat.mul x3 (Nat.add (dest_nadd x0 x1) (Nat.add x4 x5))))) /\ (~ (Peano.le (Nat.mul x1 (dest_nadd x0 x3)) (Nat.mul x1 (Nat.add (dest_nadd x2 x3) (Nat.add x4 x5))))).
Definition term248 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x1 (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.mul (Nat.add x1 x2) x3)).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((exists y1 : a0, x0 y1) /\ y0) = (exists y1 : a0, (x0 y1) /\ y0)) x1.
Definition term78 (x0 : nat) (x1 : nat) := fun y0 : nat => ((x1 = (NUMERAL 0)) \/ (Peano.le x0 y0)) = (Peano.le (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term172 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := fun y0 : nat => (fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) (Nat.add x1 x2)) (dest_nadd x3 y1))) y0.
Definition term148 (x0 : nadd) (x1 : nadd) := and (forall y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y2) y1) (dest_nadd x1 y2))) y0).
Definition term262 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term116 (x0 : nadd) := forall y0 : nadd, (~ (nadd_le x0 y0)) -> forall y1 : nat, exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd y0 y2) y1) (dest_nadd x0 y2)).
Definition term263 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x2 (dest_nadd x0 y0)) (Nat.add (Nat.mul y0 (dest_nadd x0 x2)) (Nat.mul x1 (Nat.add x2 y0)))) /\ (Peano.le (Nat.mul y0 (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul x1 (Nat.add x2 y0)))).
Definition term123 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd y0 y3)) (Nat.mul y3 (dest_nadd y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) x0.
Definition term252 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x2 (dest_nadd x0 x1)) (Nat.add (Nat.mul x1 (dest_nadd x0 x2)) (Nat.add (Nat.mul x1 x3) (Nat.mul x2 x3))).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term137 (x0 : nadd) (x1 : nadd) := ((forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y1) y0) (dest_nadd x0 y1))) /\ (forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)))) -> False.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term255 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := (Peano.le (Nat.mul x3 (dest_nadd x0 x4)) (Nat.add (Nat.mul x4 (dest_nadd x0 x3)) (Nat.mul (Nat.add x3 x4) x1))) /\ (Peano.le (Nat.mul x4 (dest_nadd x2 x3)) (Nat.add (Nat.mul x3 (dest_nadd x2 x4)) (Nat.mul (Nat.add x3 x4) x5))).
Definition term198 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := exists y0 : nat, exists y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0))).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term259 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x3 (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x1 (Nat.add x2 x3))).
Definition term128 (x0 : nadd) (x1 : nadd) := ~ (~ ((nadd_le x1 x0) \/ (nadd_le x0 x1))).
Definition term251 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x1 (dest_nadd x0 x2)) (Nat.mul (Nat.add x1 x2) x3).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Nat.add (Nat.add x0 (Nat.add x1 x2)) (Nat.add x3 (Nat.add x4 x5)).
Definition term234 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.mul x3 (dest_nadd x0 x1)) (Nat.add (Nat.mul x3 x2) (Nat.mul x3 x4)).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term134 (x0 : nadd) (x1 : nadd) := ~ (nadd_le x0 x1).
Definition term132 (x0 : nadd) (x1 : nadd) := (~ (nadd_le x1 x0)) /\ (~ (nadd_le x0 x1)).
Definition term195 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := fun y0 : nat => ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ ((~ (x4 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 x4) (Nat.add x1 x2)) (dest_nadd x3 x4))).
Definition term73 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term61 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0)) x1.
Definition term98 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ (~ x1)).
Definition term40 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (y0 = y0) = True) x0.
Definition term213 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := ~ ((x0 = (NUMERAL 0)) \/ (~ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5)))).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 (Nat.add x0 x2)) /\ (Peano.le x0 (Nat.add x1 x2)).
Definition term245 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x2 (dest_nadd x0 x1)) (Nat.mul (Nat.add x1 x2) x3).
Definition term118 (x0 : nadd) (x1 : nadd) := (~ (nadd_le x1 x0)) -> forall y0 : nat, exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)).
Definition term147 (x0 : nadd) (x1 : nadd) := forall y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y2) y1) (dest_nadd x1 y2))) y0.
Definition term220 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.mul x0 (Nat.add (dest_nadd x1 x2) (Nat.add x3 x4)).
Definition term193 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nadd) (x5 : nat) := ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x4 x0) (Nat.add x2 x3)) (dest_nadd x1 x0))) /\ ((~ (x5 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 x5) (Nat.add x2 x3)) (dest_nadd x4 x5))).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.add x0 x1) (Nat.add x2 x3).
Definition term158 (x0 : nadd) (x1 : nadd) := forall y0 : nat, (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y1) y0) (dest_nadd x0 y1))) /\ (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1))).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := @eq nat (Nat.add x0 (Nat.add x1 (Nat.add x2 (Nat.add x3 (Nat.add x4 x5))))).
Definition term182 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := ~ (exists y0 : nat, (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0)))).
Definition term267 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul y0 (dest_nadd x0 y1)) (Nat.add (Nat.mul y1 (dest_nadd x0 y0)) (Nat.mul x1 (Nat.add y0 y1)))) /\ (Peano.le (Nat.mul y1 (dest_nadd x0 y0)) (Nat.add (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul x1 (Nat.add y0 y1)))).
Definition term266 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term82 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)) = (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term81 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term16 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term177 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) (x4 : nat) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0))) x4).
Definition term180 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := fun y0 : nat => (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0))).
Definition term265 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (Nat.mul x2 (dest_nadd x0 y0)) (Nat.add (Nat.mul y0 (dest_nadd x0 x2)) (Nat.mul x1 (Nat.add x2 y0)))) /\ (Peano.le (Nat.mul y0 (dest_nadd x0 x2)) (Nat.add (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul x1 (Nat.add x2 y0)))).
Definition term163 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := ~ ((exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y0) (Nat.add x1 x2)) (dest_nadd x0 y0))) /\ (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y0) (Nat.add x1 x2)) (dest_nadd x3 y0)))).
Definition term276 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term86 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)) = (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term85 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2)).
Definition term21 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2)) = (Nat.mul (Nat.add y0 y1) y2).
Definition term20 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2)).
Definition term160 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x1 y1) y0) (dest_nadd x0 y1))) /\ (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) y0) (dest_nadd x1 y1)))) (Nat.add x2 x3).
Definition term260 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term167 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nadd) := exists y0 : nat, (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x3 y1) (Nat.add x1 x2)) (dest_nadd x0 y1))) /\ ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd x0 y1) (Nat.add x1 x2)) (dest_nadd x3 y1))) y0).
