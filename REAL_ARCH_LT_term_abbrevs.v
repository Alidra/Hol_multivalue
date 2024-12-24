Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term215 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (real_lt x0 x1))))) -> real_lt x2 x3.
Definition term229 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3))))).
Definition term62 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term125 (x0 : real) (x1 : nat) := ~ (real_lt x0 (real_of_num x1)).
Definition term105 (x0 : real) := exists y0 : nat, real_le x0 (real_of_num y0).
Definition term238 (x0 : real) (x1 : nat) := (real_lt x0 (real_of_num x1)) -> False.
Definition term148 := fun y0 : real => fun y1 : nat => real_le y0 (real_of_num y1).
Definition term129 (x0 : real -> Prop) := ~ (all x0).
Definition term241 := (~ False) -> False.
Definition term23 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term98 := imp (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term158 (x0 : real -> nat) (x1 : real) := (fun y0 : nat => real_le x1 (real_of_num y0)) (x0 x1).
Definition term152 (x0 : real) := fun y0 : nat => (fun y1 : real => fun y2 : nat => real_le y1 (real_of_num y2)) x0 y0.
Definition term172 (x0 : real) (x1 : nat) := (fun y0 : nat => ~ (real_lt x0 (real_of_num y0))) x1.
Definition term154 := fun y0 : real => exists y1 : nat, (fun y2 : real => fun y3 : nat => real_le y2 (real_of_num y3)) y0 y1.
Definition term135 := fun y0 : real => forall y1 : nat, ~ (real_lt y0 (real_of_num y1)).
Definition term28 (x0 : real) (x1 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term190 (x0 : real) (x1 : real) := (real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))) \/ (~ (real_le x0 x1)).
Definition term196 (x0 : Prop) := ~ (~ x0).
Definition term7 := real_of_num (NUMERAL 0).
Definition term102 := (~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> ~ (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)).
Definition term204 (x0 : real -> nat) (x1 : real) := ~ (real_lt x1 (real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term186 (x0 : real -> nat) (x1 : real) := (~ ((real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0)))))) -> (real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0)))).
Definition term153 (x0 : real) := exists y0 : nat, (fun y1 : real => fun y2 : nat => real_le y1 (real_of_num y2)) x0 y0.
Definition term72 (x0 : real) (x1 : real) := real_ge (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term225 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x2 = x0))) /\ (~ (~ (real_lt x1 x2))).
Definition term197 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term109 (x0 : nat) := fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term185 (x0 : real -> nat) (x1 : real) := real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0))).
Definition term49 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term203 (x0 : real -> nat) (x1 : real) := (~ (real_lt x1 (real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))))) -> real_lt x1 (real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term14 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term100 := (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> ~ (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)).
Definition term56 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term136 := exists y0 : real, forall y1 : nat, ~ (real_lt y0 (real_of_num y1)).
Definition term184 (x0 : real -> nat) (x1 : real) := real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term84 (x0 : Prop) := (~ x0) -> False.
Definition term79 (x0 : real) (x1 : real) := (~ ((real_le x0 x1) -> real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))) -> False.
Definition term107 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num x1).
Definition term82 (x0 : real) := forall y0 : real, (real_le x0 y0) -> real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term13 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term150 (x0 : real) (x1 : nat) := (fun y0 : real => fun y1 : nat => real_le y0 (real_of_num y1)) x0 x1.
Definition term194 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term54 (x0 : real) (x1 : real) := real_ge (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term201 (x0 : real -> nat) (x1 : real) := real_of_num (x0 x1).
Definition term181 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term57 (x0 : real) := real_add x0 (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term183 (x0 : Prop) := (~ x0) -> x0.
Definition term21 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term44 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term78 := and ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term227 (x0 : real) (x1 : real) (x2 : real) := (x2 = x0) /\ (real_lt x1 x2).
Definition term218 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term142 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term160 (x0 : real -> nat) := fun y0 : real => (fun y1 : real => fun y2 : nat => real_le y1 (real_of_num y2)) y0 (x0 y0).
Definition term39 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term237 (x0 : real -> nat) (x1 : real) := ~ (real_lt x1 (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0))))).
Definition term99 := (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False.
Definition term141 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term83 := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term70 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term68 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term166 := exists y0 : real -> nat, forall y1 : real, real_le y1 (real_of_num (y0 y1)).
Definition term147 := exists y0 : real -> nat, forall y1 : real, (fun y2 : real => fun y3 : nat => real_le y2 (real_of_num y3)) y1 (y0 y1).
Definition term145 (x0 : type1622) := exists y0 : real -> nat, forall y1 : real, x0 y1 (y0 y1).
Definition term161 (x0 : real -> nat) := fun y0 : real => real_le y0 (real_of_num (x0 y0)).
Definition term96 := (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False.
Definition term11 (x0 : real) := real_add x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term50 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term81 (x0 : real) (x1 : real) := (real_le x0 x1) -> real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term205 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term234 (x0 : real -> nat) (x1 : real) := ((x1 = x1) /\ (((real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0))))) /\ (real_lt x1 (real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0))))))) -> real_lt x1 (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0)))).
Definition term157 (x0 : real -> nat) (x1 : real) := (fun y0 : real => fun y1 : nat => real_le y0 (real_of_num y1)) x1 (x0 x1).
Definition term170 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0))) x1.
Definition term76 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term131 := exists y0 : real, ~ ((fun y1 : real => exists y2 : nat, real_lt y1 (real_of_num y2)) y0).
Definition term15 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term132 (x0 : real) := (fun y0 : real => exists y1 : nat, real_lt y0 (real_of_num y1)) x0.
Definition term230 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x2 = x0) /\ ((x3 = x1) /\ (real_lt x2 x3))).
Definition term75 (x0 : nat) (x1 : nat) := real_ge (real_neg (real_of_num x0)) (real_of_num x1).
Definition term128 (x0 : real) := forall y0 : nat, ~ (real_lt x0 (real_of_num y0)).
Definition term134 := fun y0 : real => ~ ((fun y1 : real => exists y2 : nat, real_lt y1 (real_of_num y2)) y0).
Definition term206 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3))).
Definition term41 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term211 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3)))).
Definition term116 (x0 : real) := fun y0 : nat => real_lt x0 (real_of_num y0).
Definition term140 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term114 := fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term8 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term162 (x0 : real -> nat) := forall y0 : real, (fun y1 : real => fun y2 : nat => real_le y1 (real_of_num y2)) y0 (x0 y0).
Definition term92 := (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False.
Definition term179 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) -> (~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3))).
Definition term60 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term24 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term163 (x0 : real -> nat) := forall y0 : real, real_le y0 (real_of_num (x0 y0)).
Definition term187 (x0 : real -> nat) (x1 : real) := ~ ((real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0))))).
Definition term207 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term210 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((real_lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3)))).
Definition term91 := (((~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False) -> (~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False) -> ((~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False) -> (~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False.
Definition term93 := ~ (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)).
Definition term87 := ~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1)).
Definition term1 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ (real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term89 := ((~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False) -> (~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False.
Definition term208 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term178 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3))).
Definition term212 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = x0)) \/ (~ (real_lt x1 x2)).
Definition term139 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) \/ (real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term174 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt x2 x3) = (real_lt x0 x1)) -> (real_lt x0 x1) \/ (~ (real_lt x2 x3)).
Definition term156 := @eq Prop (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)).
Definition term155 := @eq Prop (forall y0 : real, exists y1 : nat, (fun y2 : real => fun y3 : nat => real_le y2 (real_of_num y3)) y0 y1).
Definition term214 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3))))).
Definition term200 (x0 : real -> nat) (x1 : real) := (real_le x1 (real_of_num (x0 x1))) -> real_lt x1 (real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term47 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term29 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term217 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term112 := forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term159 (x0 : real -> nat) (x1 : real) := real_le x1 (real_of_num (x0 x1)).
Definition term65 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term31 (x0 : real) (x1 : real) := real_ge (real_sub x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term133 (x0 : real) := ~ ((fun y0 : real => exists y1 : nat, real_lt y0 (real_of_num y1)) x0).
Definition term18 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term119 (x0 : nat -> Prop) := ~ (ex x0).
Definition term90 := (((~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False) -> (~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False) -> (~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False.
Definition term69 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term80 (x0 : real) (x1 : real) := ((~ ((real_le x0 x1) -> real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))) -> False) -> (real_le x0 x1) -> real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term115 (x0 : real) (x1 : nat) := real_lt x0 (real_of_num x1).
Definition term146 := forall y0 : real, exists y1 : nat, (fun y2 : real => fun y3 : nat => real_le y2 (real_of_num y3)) y0 y1.
Definition term144 (x0 : type1622) := forall y0 : real, exists y1 : nat, x0 y0 y1.
Definition term94 := forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1).
Definition term85 := forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1).
Definition term52 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term42 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term77 := ((NUMERAL (BIT1 0)) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)).
Definition term239 (x0 : real -> nat) (x1 : real) := (real_lt x1 (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0))))) -> False.
Definition term10 (x0 : real) (x1 : real) := real_ge (real_sub x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term130 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term120 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term167 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0)))))) x0.
Definition term189 (x0 : real -> nat) (x1 : real) := ~ (real_le x1 (real_of_num (x0 x1))).
Definition term236 (x0 : real -> nat) (x1 : real) := (~ (real_lt x1 (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0)))))) -> real_lt x1 (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0)))).
Definition term73 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term37 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term6 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term40 := S (Nat.add 0 0).
Definition term219 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3)))).
Definition term59 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term51 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term16 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term86 := (~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> False.
Definition term20 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term32 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term88 := (~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)) -> False.
Definition term5 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1).
Definition term36 (x0 : real) (x1 : real) := (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term55 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term103 (x0 : real) (x1 : nat) := real_le x0 (real_of_num x1).
Definition term63 := real_mul (real_of_num (NUMERAL 0)).
Definition term123 (x0 : real) (x1 : nat) := (fun y0 : nat => real_lt x0 (real_of_num y0)) x1.
Definition term113 (x0 : real) := fun y0 : real => (real_le x0 y0) -> real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term30 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term222 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term173 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term53 (x0 : real) (x1 : real) := ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term48 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term43 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term117 (x0 : real) := exists y0 : nat, real_lt x0 (real_of_num y0).
Definition term118 := fun y0 : real => exists y1 : nat, real_lt y0 (real_of_num y1).
Definition term106 := fun y0 : real => exists y1 : nat, real_le y0 (real_of_num y1).
Definition term19 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term226 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term127 (x0 : real) := fun y0 : nat => ~ (real_lt x0 (real_of_num y0)).
Definition term122 (x0 : real) := forall y0 : nat, ~ ((fun y1 : nat => real_lt x0 (real_of_num y1)) y0).
Definition term12 (x0 : real) (x1 : real) := real_sub x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term169 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) x0.
Definition term33 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term233 (x0 : real -> nat) (x1 : real) := (x1 = x1) /\ (((real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0))))) /\ (real_lt x1 (real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term104 (x0 : real) := fun y0 : nat => real_le x0 (real_of_num y0).
Definition term165 := fun y0 : real -> nat => forall y1 : real, real_le y1 (real_of_num (y0 y1)).
Definition term164 := fun y0 : real -> nat => forall y1 : real, (fun y2 : real => fun y3 : nat => real_le y2 (real_of_num y3)) y1 (y0 y1).
Definition term235 (x0 : real -> nat) (x1 : real) := real_lt x1 (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0)))).
Definition term199 (x0 : real) (x1 : real) := imp (real_le x0 x1).
Definition term191 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term25 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term216 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3))).
Definition term240 (x0 : real -> nat) (x1 : real) := Nat.add (x0 x1) (NUMERAL (BIT1 0)).
Definition term224 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x2 = x0)) \/ (~ (real_lt x1 x2))).
Definition term110 (x0 : nat) := forall y0 : nat, (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term17 := real_of_num (NUMERAL (BIT1 0)).
Definition term138 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) \/ (real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term192 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x0 x1)) \/ (real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term26 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term213 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3))))).
Definition term46 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term71 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term223 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term64 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term2 (x0 : real) (x1 : real) := real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term9 (x0 : real) (x1 : real) := ~ (real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term97 := (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> ~ (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)).
Definition term34 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term177 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term182 (x0 : real) := ~ (x0 = x0).
Definition term220 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (real_lt x2 x3)))).
Definition term176 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x3 = x1) -> (real_lt x0 x1) \/ (~ (real_lt x2 x3)).
Definition term137 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ (real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term45 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term35 (x0 : real) (x1 : real) := and (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term193 (x0 : real) (x1 : real) := @eq Prop ((real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))) \/ (~ (real_le x0 x1))).
Definition term111 := fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term228 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) /\ ((x3 = x1) /\ (real_lt x2 x3)).
Definition term168 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_le x0 y0)) \/ (real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0)))))) x1.
Definition term151 (x0 : real) (x1 : nat) := (fun y0 : nat => real_le x0 (real_of_num y0)) x1.
Definition term202 (x0 : real -> nat) (x1 : real) := real_lt x1 (real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term126 (x0 : real) := fun y0 : nat => ~ ((fun y1 : nat => real_lt x0 (real_of_num y1)) y0).
Definition term124 (x0 : real) (x1 : nat) := ~ ((fun y0 : nat => real_lt x0 (real_of_num y0)) x1).
Definition term175 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt x0 x1) \/ (~ (real_lt x2 x3)).
Definition term27 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term221 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term61 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term232 (x0 : real -> nat) (x1 : real) := ((real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0))))) /\ (real_lt x1 (real_add (real_of_num (x0 x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term74 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term209 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term143 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term188 (x0 : real -> nat) (x1 : real) := (~ (real_le x1 (real_of_num (x0 x1)))) -> real_le x1 (real_of_num (x0 x1)).
Definition term95 := imp (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))).
Definition term66 := real_add (real_of_num (NUMERAL 0)).
Definition term108 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 x1).
Definition term180 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_lt x0 x1) \/ (~ (real_lt x2 x3)))).
Definition term149 (x0 : real) := (fun y0 : real => fun y1 : nat => real_le y0 (real_of_num y1)) x0.
Definition term67 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x0 (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term121 (x0 : real) := ~ (exists y0 : nat, real_lt x0 (real_of_num y0)).
Definition term171 (x0 : real -> nat) (x1 : real) := (fun y0 : real => real_le y0 (real_of_num (x0 y0))) x1.
Definition term22 := NUMERAL (BIT1 0).
Definition term231 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ ((x1 = x3) /\ (real_lt x0 x1))) -> real_lt x2 x3.
Definition term101 := imp (~ (forall y0 : real, exists y1 : nat, real_lt y0 (real_of_num y1))).
Definition term58 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term38 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term0 (x0 : real) (x1 : real) := ~ ((real_le x0 x1) -> real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term198 (x0 : real) (x1 : real) := imp (~ (~ (real_le x0 x1))).
Definition term3 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term195 (x0 : real) (x1 : real) := (~ (~ (real_le x0 x1))) -> real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))).
