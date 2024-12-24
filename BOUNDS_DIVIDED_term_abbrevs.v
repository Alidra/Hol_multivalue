Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term213 (x0 : nat -> nat) := (exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) y0) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 (x0 y2)) (Nat.add (Nat.mul y0 y2) y1).
Definition term212 (x0 : nat -> nat) := (exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 (x0 y2)) (Nat.add (Nat.mul y0 y2) y1)) -> exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) y0.
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term208 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := fun y0 : nat => (Peano.le (Nat.mul x0 (x1 x0)) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))).
Definition term64 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 (x1 x0)) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le (x1 x0) y0))) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)).
Definition term89 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (x1 = (NUMERAL 0)) \/ (Peano.le (x0 x1) x2).
Definition term13 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term113 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul (NUMERAL 0) (x0 (NUMERAL 0))) (Nat.mul (NUMERAL 0) (Nat.add (x0 (NUMERAL 0)) (Nat.add x1 x2)))) -> True.
Definition term202 (x0 : nat) := imp (~ ((S x0) = (NUMERAL 0))).
Definition term197 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term94 (x0 : nat -> nat) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 (x0 y2)) (Nat.add (Nat.mul y0 y2) y1).
Definition term163 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 x1).
Definition term75 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (Nat.mul y1 (x0 y1)) (Nat.add (Nat.mul x1 y1) y0).
Definition term72 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) y0.
Definition term80 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 (x0 x2)) (Nat.mul x1 x2).
Definition term105 := @eq nat (NUMERAL 0).
Definition term191 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term60 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term50 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term41 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term35 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.le y1 y2)) x0.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term154 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.mul x0 x1).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0)) x2.
Definition term210 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (x0 y0) (Nat.add (x0 (NUMERAL 0)) (Nat.add x1 x2)).
Definition term18 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term78 (x0 : nat -> nat) (x1 : nat) := Peano.le (Nat.mul x1 (x0 x1)).
Definition term91 (x0 : nat) := (x0 = (NUMERAL 0)) \/ True.
Definition term162 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) x1.
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term107 (x0 : nat -> nat) := Peano.le (x0 (NUMERAL 0)).
Definition term196 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term138 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term188 (x0 : nat) := Peano.le x0 (Nat.mul x0 (NUMERAL 0)).
Definition term193 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term119 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (fun y0 : Prop => y0) (Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3))).
Definition term153 (x0 : nat) (x1 : nat) := (Peano.le x0 (Nat.mul x0 x1)) /\ True.
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add (Nat.add (Nat.mul x0 x3) (Nat.mul x1 x3)) (Nat.mul (x2 (NUMERAL 0)) x3).
Definition term201 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 (Nat.mul x0 x1)).
Definition term161 (x0 : nat) := and ((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (NUMERAL 0))).
Definition term38 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0).
Definition term179 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0.
Definition term12 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term174 (x0 : nat) := ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) (S y0)).
Definition term98 (x0 : nat -> nat) := Nat.mul (NUMERAL 0) (x0 (NUMERAL 0)).
Definition term136 (x0 : nat) (x1 : nat -> nat) := Nat.mul x0 (x1 (NUMERAL 0)).
Definition term129 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := True /\ (Peano.le (Nat.add (Nat.mul x2 x0) x3) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))).
Definition term118 := fun y0 : Prop => y0.
Definition term16 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term125 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x2 (x0 x2)) (Nat.add (Nat.mul x1 x2) x3).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x1 x0) (Nat.add x1 x2).
Definition term70 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term168 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) x1) -> (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (S x1).
Definition term158 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (NUMERAL 0).
Definition term156 (x0 : nat) := (((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0.
Definition term23 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term102 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (NUMERAL 0) (x0 (NUMERAL 0))) (Nat.mul (NUMERAL 0) (Nat.add (x0 (NUMERAL 0)) (Nat.add x1 x2))).
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)).
Definition term111 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := imp (Peano.le (Nat.mul (NUMERAL 0) (x0 (NUMERAL 0))) (Nat.mul (NUMERAL 0) (Nat.add (x0 (NUMERAL 0)) (Nat.add x1 x2)))).
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term155 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term88 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (x0 x1) x2.
Definition term176 (x0 : nat) := imp (((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) (S y0))).
Definition term25 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term92 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul y0 (x0 y0)) (Nat.add (Nat.mul x1 y0) (NUMERAL 0)).
Definition term87 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (x0 y0) x1) x2.
Definition term71 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term180 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul x0 x3) x1) (Nat.add (Nat.mul x0 x3) (Nat.add (Nat.mul x1 x3) (Nat.mul (x2 (NUMERAL 0)) x3))).
Definition term203 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> True.
Definition term67 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3))).
Definition term186 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term76 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (Nat.mul y0 (x0 y0)) (Nat.add (Nat.mul x1 y0) x2).
Definition term82 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term37 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1)) x1.
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term165 (x0 : nat) (x1 : nat) := imp ((~ (x1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 x1)).
Definition term122 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := @eq Prop (Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3))).
Definition term172 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) (S y0).
Definition term59 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term93 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y1 (x0 y1)) (Nat.add (Nat.mul x1 y1) y0).
Definition term27 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term151 (x0 : nat) (x1 : nat) := and (Peano.le x0 (Nat.mul x0 x1)).
Definition term198 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term148 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul (x1 (NUMERAL 0)) x2).
Definition term150 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Peano.le (Nat.mul x0 x2) (Nat.add (Nat.mul x0 x2) (Nat.mul (x1 (NUMERAL 0)) x2)).
Definition term69 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term160 (x0 : nat) := and ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (NUMERAL 0)).
Definition term214 (x0 : nat -> nat) := ((exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) y0) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 (x0 y2)) (Nat.add (Nat.mul y0 y2) y1)) /\ ((exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 (x0 y2)) (Nat.add (Nat.mul y0 y2) y1)) -> exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) y0).
Definition term167 (x0 : nat) (x1 : nat) := (~ ((S x1) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S x1)).
Definition term184 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term132 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x2 (x0 (NUMERAL 0))) (Nat.add (Nat.mul x2 x1) (Nat.mul x2 x3)).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term170 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0) -> (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) (S y0).
Definition term116 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := imp ((Peano.le (Nat.mul x0 (x1 x0)) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))) = (Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))).
Definition term178 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (y1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y1)) y0.
Definition term169 (x0 : nat) (x1 : nat) := ((~ (x1 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 x1)) -> (~ ((S x1) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S x1)).
Definition term200 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.mul x0 (S x1)).
Definition term104 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.le (Nat.mul (NUMERAL 0) (x0 (NUMERAL 0))) (Nat.mul (NUMERAL 0) (Nat.add (x0 (NUMERAL 0)) (Nat.add x1 x2)))).
Definition term90 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term128 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul x0 (x1 x0)) (Nat.add (Nat.mul x2 x0) x3)) /\ (Peano.le (Nat.add (Nat.mul x2 x0) x3) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))).
Definition term115 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := False \/ (Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3))).
Definition term194 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term61 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term51 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term36 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1).
Definition term34 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term33 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term30 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term29 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term17 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term6 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term4 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term58 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term166 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) (S x1).
Definition term109 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (x0 (NUMERAL 0)) (Nat.add (x0 (NUMERAL 0)) (Nat.add x1 x2)).
Definition term181 (x0 : nat) := (((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (NUMERAL 0))) /\ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S y0)))) -> forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0).
Definition term124 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (Nat.mul y0 (x0 y0)) (Nat.add (Nat.mul x1 y0) x2)) x3.
Definition term127 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul x2 x0) x3) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3))).
Definition term164 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) x1).
Definition term126 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := and (Peano.le (Nat.mul x2 (x0 x2)) (Nat.add (Nat.mul x1 x2) x3)).
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term83 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term63 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x1 (x0 x1)) (Nat.mul x1 y0)) = ((x1 = (NUMERAL 0)) \/ (Peano.le (x0 x1) y0)).
Definition term53 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term147 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Peano.le x0 (Nat.add (Nat.mul x0 x2) (Nat.mul (x1 (NUMERAL 0)) x2)).
Definition term204 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term159 (x0 : nat) := (~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (NUMERAL 0)).
Definition term99 (x0 : nat -> nat) := Peano.le (Nat.mul (NUMERAL 0) (x0 (NUMERAL 0))).
Definition term97 (x0 : nat -> nat) (x1 : nat) := Nat.mul x1 (x0 x1).
Definition term48 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term45 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add (Nat.mul x0 x3) (Nat.add (Nat.mul x1 x3) (Nat.mul (x2 (NUMERAL 0)) x3)).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term120 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (fun y0 : Prop => y0) (Peano.le (Nat.mul x0 (x1 x0)) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) := Nat.add (Nat.add (Nat.mul x2 x0) (Nat.mul x2 x1)) (Nat.mul x2 (x3 (NUMERAL 0))).
Definition term190 (x0 : nat) := False -> Peano.le x0 (NUMERAL 0).
Definition term66 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x0 (x1 x0)) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3))).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term46 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term207 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := exists y0 : nat, (Peano.le (Nat.mul x0 (x1 x0)) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))).
Definition term205 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 (Nat.add (Nat.mul x0 x2) (Nat.mul (x1 (NUMERAL 0)) x2))).
Definition term192 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term68 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term8 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2)).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term81 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 (x0 x1)) (Nat.mul x1 x2).
Definition term131 (x0 : nat) (x1 : nat -> nat) := Nat.add (Nat.mul x0 (x1 (NUMERAL 0))).
Definition term211 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (x0 y1) y0.
Definition term171 (x0 : nat) := fun y0 : nat => ((~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S y0)).
Definition term149 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 (Nat.add (Nat.mul x0 x2) (Nat.mul (x1 (NUMERAL 0)) x2)))) -> Peano.le x0 (Nat.add (Nat.mul x0 x2) (Nat.mul (x1 (NUMERAL 0)) x2)).
Definition term96 (x0 : nat -> nat) := x0 (NUMERAL 0).
Definition term187 := imp (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term65 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (x0 (NUMERAL 0)) (Nat.add x1 x2).
Definition term108 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)).
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x0 x1) x2).
Definition term195 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term44 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term100 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)).
Definition term175 (x0 : nat) := ((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (NUMERAL 0))) /\ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S y0))).
Definition term183 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term123 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (exists y0 : nat, (Peano.le (Nat.mul x0 (x1 x0)) y0) /\ (Peano.le y0 (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3))))) -> Peano.le (Nat.mul x0 (x1 x0)) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3))).
Definition term199 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term185 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term215 := forall y0 : nat -> nat, (exists y1 : nat, forall y2 : nat, Peano.le (y0 y2) y1) = (exists y1 : nat, exists y2 : nat, forall y3 : nat, Peano.le (Nat.mul y3 (y0 y3)) (Nat.add (Nat.mul y1 y3) y2)).
Definition term79 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 (x0 x2)) (Nat.add (Nat.mul x1 x2) (NUMERAL 0)).
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term157 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0).
Definition term62 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x1 y0) (Nat.mul x1 y1)) = ((x1 = (NUMERAL 0)) \/ (Peano.le y0 y1))) (x0 x1).
Definition term15 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term106 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 x1).
Definition term134 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul x1 x2) x3) (Nat.add (Nat.mul x2 (x0 (NUMERAL 0))) (Nat.add (Nat.mul x2 x1) (Nat.mul x2 x3))).
Definition term114 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term117 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := ((Peano.le (Nat.mul x0 (x1 x0)) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))) = (Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))) -> Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)).
Definition term112 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := ((Peano.le (Nat.mul x0 (x1 x0)) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))) = ((x0 = (NUMERAL 0)) \/ (Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3))))) -> Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)).
Definition term121 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : Prop => y0) (Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))).
Definition term177 (x0 : nat) := imp (((~ ((NUMERAL 0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (NUMERAL 0))) /\ (forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S y0)))).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term26 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul x0 x3) x1) (Nat.add (Nat.add (Nat.mul x0 x3) (Nat.mul x1 x3)) (Nat.mul (x2 (NUMERAL 0)) x3)).
Definition term14 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term130 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x1 (x0 (NUMERAL 0))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term74 (x0 : nat -> nat) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (Nat.mul y2 (x0 y2)) (Nat.add (Nat.mul y0 y2) y1).
Definition term152 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (Peano.le x0 (Nat.mul x0 x2)) /\ (Peano.le (Nat.mul x0 x2) (Nat.add (Nat.mul x0 x2) (Nat.mul (x1 (NUMERAL 0)) x2))).
Definition term95 := Nat.mul (NUMERAL 0).
Definition term173 (x0 : nat) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 y0)) -> (~ ((S y0) = (NUMERAL 0))) -> Peano.le x0 (Nat.mul x0 (S y0)).
Definition term142 (x0 : nat -> nat) (x1 : nat) := Nat.mul (x0 (NUMERAL 0)) x1.
Definition term209 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term110 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := imp ((Peano.le (Nat.mul x0 (x1 x0)) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))) = ((x0 = (NUMERAL 0)) \/ (Peano.le (x1 x0) (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3))))).
Definition term206 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 (Nat.add (Nat.mul x0 x2) (Nat.mul (x1 (NUMERAL 0)) x2))).
Definition term24 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term77 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) (NUMERAL 0).
Definition term103 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := @eq Prop (Peano.le (Nat.mul x0 (x1 x0)) (Nat.mul x0 (Nat.add (x1 (NUMERAL 0)) (Nat.add x2 x3)))).
Definition term73 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, Peano.le (x0 y0) x1.
Definition term189 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term182 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) := Peano.le (Nat.add (Nat.mul x0 x2) x1) (Nat.add (Nat.add (Nat.mul x2 x0) (Nat.mul x2 x1)) (Nat.mul x2 (x3 (NUMERAL 0)))).
Definition term57 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term28 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term101 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.mul (NUMERAL 0) (Nat.add (x0 (NUMERAL 0)) (Nat.add x1 x2)).
Definition term32 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term31 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
