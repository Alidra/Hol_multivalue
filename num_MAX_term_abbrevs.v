Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term122 (x0 : nat -> Prop) := fun y0 : nat => x0 y0.
Definition term82 (x0 : nat -> Prop) (x1 : nat) := ((forall y0 : nat, (x0 y0) -> Peano.le y0 (S x1)) /\ (forall y0 : nat, (Peano.lt y0 (S x1)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> x0 (S x1).
Definition term92 (x0 : nat -> Prop) := imp ((((forall y0 : nat, (x0 y0) -> Peano.le y0 (NUMERAL 0)) /\ (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> x0 (NUMERAL 0)) /\ (forall y0 : nat, (((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) -> ((forall y1 : nat, (x0 y1) -> Peano.le y1 (S y0)) /\ (forall y1 : nat, (Peano.lt y1 (S y0)) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 (S y0))).
Definition term153 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((x0 x1) -> Peano.le x1 (S x2)) -> (x0 x1) -> Peano.le x1 x2.
Definition term132 (x0 : nat) := Peano.lt x0 (S x0).
Definition term44 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (x0 y1) -> Peano.le y1 y0.
Definition term19 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term37 (x0 : Prop) (x1 : Prop) := @eq Prop (x0 -> x1).
Definition term145 (x0 : Prop) := ~ (~ x0).
Definition term152 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x1) -> Peano.le x1 x2.
Definition term176 := forall y0 : nat -> Prop, ((exists y1 : nat, y0 y1) /\ (exists y1 : nat, forall y2 : nat, (y0 y2) -> Peano.le y2 y1)) = (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (y0 y2) -> Peano.le y2 y1)).
Definition term175 (x0 : nat -> Prop) := (((exists y0 : nat, x0 y0) /\ (exists y0 : nat, forall y1 : nat, (x0 y1) -> Peano.le y1 y0)) -> exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0)) /\ ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0)) -> (exists y0 : nat, x0 y0) /\ (exists y0 : nat, forall y1 : nat, (x0 y1) -> Peano.le y1 y0)).
Definition term43 (x0 : nat -> Prop) := (exists y0 : nat, x0 y0) /\ (exists y0 : nat, forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term161 (x0 : nat) := False -> Peano.le (S x0) x0.
Definition term62 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> ~ ((fun y1 : nat => forall y2 : nat, (x1 y2) -> Peano.le y2 y1) y0).
Definition term27 (x0 : Prop) (x1 : Prop) := (True /\ x0) -> x1.
Definition term113 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term88 (x0 : nat -> Prop) := forall y0 : nat, (((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) -> ((forall y1 : nat, (x0 y1) -> Peano.le y1 (S y0)) /\ (forall y1 : nat, (Peano.lt y1 (S y0)) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 (S y0).
Definition term77 (x0 : nat -> Prop) := and (((forall y0 : nat, (x0 y0) -> Peano.le y0 (NUMERAL 0)) /\ (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> x0 (NUMERAL 0)).
Definition term134 (x0 : nat) := or (x0 = x0).
Definition term150 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := imp ((x0 x1) -> Peano.le x1 (S x2)).
Definition term173 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (x0 y0) -> Peano.le y0 x1.
Definition term157 (x0 : nat) (x1 : nat) := or (x0 = (S x1)).
Definition term98 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> Peano.le x1 (NUMERAL 0).
Definition term55 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (x0 y1) -> Peano.le y1 y0) x1).
Definition term141 (x0 : nat -> Prop) (x1 : nat) := ((Peano.lt x1 (S x1)) -> ~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1)) -> x0 (S x1).
Definition term86 (x0 : nat -> Prop) := fun y0 : nat => (((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) -> ((forall y1 : nat, (x0 y1) -> Peano.le y1 (S y0)) /\ (forall y1 : nat, (Peano.lt y1 (S y0)) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 (S y0).
Definition term40 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) = (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)))) x0.
Definition term52 (x0 : nat -> Prop) := @eq Prop (exists y0 : nat, forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term174 (x0 : nat -> Prop) := (exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0)) -> (exists y0 : nat, x0 y0) /\ (exists y0 : nat, forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term94 (x0 : nat -> Prop) := forall y0 : nat, (fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) y0.
Definition term97 (x0 : nat -> Prop) (x1 : nat) := imp (x0 x1).
Definition term38 (x0 : Prop) := imp (False /\ x0).
Definition term46 (x0 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => forall y2 : nat, (x0 y2) -> Peano.le y2 y1) y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ ((fun y2 : nat => forall y3 : nat, (x0 y3) -> Peano.le y3 y2) y1)).
Definition term89 (x0 : nat -> Prop) := ((fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) y0) -> (fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) (S y0)).
Definition term138 (x0 : nat -> Prop) (x1 : nat) := imp ((Peano.lt x1 (S x1)) -> ~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1)).
Definition term31 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop (((x0 /\ x1) -> x2 /\ x0) = ((x0 /\ x1) -> x2)).
Definition term56 (x0 : nat -> Prop) (x1 : nat) := ~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1).
Definition term148 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x1) -> Peano.le x1 (S x2).
Definition term67 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1)).
Definition term35 (x0 : Prop) := imp (True /\ x0).
Definition term84 (x0 : nat -> Prop) (x1 : nat) := (((forall y0 : nat, (x0 y0) -> Peano.le y0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> x0 x1) -> ((forall y0 : nat, (x0 y0) -> Peano.le y0 (S x1)) /\ (forall y0 : nat, (Peano.lt y0 (S x1)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> x0 (S x1).
Definition term83 (x0 : nat -> Prop) (x1 : nat) := ((fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) x1) -> (fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) (S x1).
Definition term72 (x0 : nat -> Prop) := (((fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) y0) -> (fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) y0.
Definition term29 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x2 /\ x0) -> x1 /\ x2.
Definition term15 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term160 (x0 : nat) := True \/ (Peano.le (S x0) x0).
Definition term95 (x0 : nat -> Prop) := forall y0 : nat, ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0.
Definition term71 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term136 (x0 : nat) := imp (Peano.lt x0 (S x0)).
Definition term63 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> ~ (forall y1 : nat, (x1 y1) -> Peano.le y1 y0).
Definition term91 (x0 : nat -> Prop) := imp (((fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) y0) -> (fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) (S y0))).
Definition term106 (x0 : nat) := imp (Peano.lt x0 (NUMERAL 0)).
Definition term133 (x0 : nat) := (x0 = x0) \/ (Peano.lt x0 x0).
Definition term143 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (S x1))) -> ~ (~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1)).
Definition term128 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 (S x0)) -> ~ (forall y1 : nat, (x1 y1) -> Peano.le y1 y0).
Definition term111 (x0 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term100 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) -> Peano.le y0 (NUMERAL 0).
Definition term66 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (x0 y2) -> Peano.le y2 y1) y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ ((fun y2 : nat => forall y3 : nat, (x0 y3) -> Peano.le y3 y2) y1)).
Definition term48 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (x0 y1) -> Peano.le y1 y0) x1.
Definition term166 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) /\ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1).
Definition term87 (x0 : nat -> Prop) := forall y0 : nat, ((fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) y0) -> (fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) (S y0).
Definition term49 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (x0 y0) -> Peano.le y0 x1.
Definition term47 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (x0 y1) -> Peano.le y1 y0.
Definition term14 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term81 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) (S x1).
Definition term171 (x0 : nat -> Prop) := ((exists y0 : nat, x0 y0) /\ (exists y0 : nat, forall y1 : nat, (x0 y1) -> Peano.le y1 y0)) -> exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term93 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) y0.
Definition term116 (x0 : nat -> Prop) := (forall y0 : nat, (x0 y0) -> y0 = (NUMERAL 0)) /\ True.
Definition term41 (x0 : nat -> Prop) := exists y0 : nat, x0 y0.
Definition term165 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((x0 x1) -> Peano.le x1 x2) -> (x0 x1) -> Peano.le x1 x2.
Definition term76 (x0 : nat -> Prop) := and ((fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) (NUMERAL 0)).
Definition term32 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 /\ x0) -> x1 /\ y0) = ((y0 /\ x0) -> x1)) False.
Definition term103 (x0 : nat -> Prop) := forall y0 : nat, (x0 y0) -> y0 = (NUMERAL 0).
Definition term102 (x0 : nat -> Prop) := forall y0 : nat, (x0 y0) -> Peano.le y0 (NUMERAL 0).
Definition term101 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) -> y0 = (NUMERAL 0).
Definition term16 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term118 (x0 : nat -> Prop) := imp (forall y0 : nat, (x0 y0) -> y0 = (NUMERAL 0)).
Definition term105 (x0 : nat -> Prop) := and (forall y0 : nat, (x0 y0) -> y0 = (NUMERAL 0)).
Definition term104 (x0 : nat -> Prop) := and (forall y0 : nat, (x0 y0) -> Peano.le y0 (NUMERAL 0)).
Definition term54 (x0 : nat -> Prop) (x1 : nat) := and (forall y0 : nat, (x0 y0) -> Peano.le y0 x1).
Definition term120 (x0 : nat -> Prop) := (forall y0 : nat, (x0 y0) -> y0 = (NUMERAL 0)) -> x0 (NUMERAL 0).
Definition term85 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) y0) -> (fun y1 : nat => ((forall y2 : nat, (x0 y2) -> Peano.le y2 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (forall y3 : nat, (x0 y3) -> Peano.le y3 y2))) -> x0 y1) (S y0).
Definition term147 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 y0) -> Peano.le y0 (S x1)) x2.
Definition term144 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 (S x1)).
Definition term117 (x0 : nat -> Prop) := imp ((forall y0 : nat, (x0 y0) -> Peano.le y0 (NUMERAL 0)) /\ (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))).
Definition term126 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (x0 x1).
Definition term80 (x0 : nat -> Prop) (x1 : nat) := imp (((forall y0 : nat, (x0 y0) -> Peano.le y0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> x0 x1).
Definition term169 (x0 : nat) (x1 : nat -> Prop) := ((forall y0 : nat, (x1 y0) -> Peano.le y0 x0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (forall y1 : nat, (x1 y1) -> Peano.le y1 y0))) -> exists y0 : nat, (x1 y0) /\ (forall y1 : nat, (x1 y1) -> Peano.le y1 y0).
Definition term23 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => ((y0 /\ x0) -> x1 /\ y0) = ((y0 /\ x0) -> x1).
Definition term9 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term3 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term168 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term123 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term13 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term112 := forall y0 : nat, True.
Definition term163 (x0 : nat) (x1 : nat) := False \/ (Peano.le x0 x1).
Definition term79 (x0 : nat -> Prop) (x1 : nat) := imp ((fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) x1).
Definition term75 (x0 : nat -> Prop) := ((forall y0 : nat, (x0 y0) -> Peano.le y0 (NUMERAL 0)) /\ (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> x0 (NUMERAL 0).
Definition term121 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 y0) -> y0 = (NUMERAL 0)) x1.
Definition term73 (x0 : nat -> Prop) := fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0.
Definition term68 (x0 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1)).
Definition term108 (x0 : nat -> Prop) (x1 : nat) := False -> ~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1).
Definition term110 := fun y0 : nat => True.
Definition term11 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term5 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term146 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1)).
Definition term131 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (x0 y0) -> Peano.le y0 (S x1).
Definition term142 (x0 : nat -> Prop) (x1 : nat) := (~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1)) -> x0 (S x1).
Definition term172 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 y0) -> Peano.le y0 x1) x2.
Definition term26 (x0 : Prop) (x1 : Prop) := (True /\ x0) -> x1 /\ True.
Definition term130 (x0 : nat -> Prop) (x1 : nat) := (Peano.lt x1 (S x1)) -> ~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1).
Definition term124 (x0 : nat -> Prop) := (fun y0 : nat => x0 y0) (NUMERAL 0).
Definition term33 (x0 : Prop) (x1 : Prop) := (False /\ x0) -> x1 /\ False.
Definition term57 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term22 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term30 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term1 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (~ (x0 = (S x1))).
Definition term53 (x0 : nat -> Prop) (x1 : nat) := and ((fun y0 : nat => forall y1 : nat, (x0 y1) -> Peano.le y1 y0) x1).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term60 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) -> ~ ((fun y1 : nat => forall y2 : nat, (x1 y2) -> Peano.le y2 y1) y0).
Definition term69 (x0 : nat -> Prop) (x1 : nat) := ((forall y0 : nat, (x0 y0) -> Peano.le y0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> (x0 x1) /\ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1).
Definition term127 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, (x1 y0) -> Peano.le y0 (S x0)) /\ (forall y0 : nat, (Peano.lt y0 (S x0)) -> ~ (forall y1 : nat, (x1 y1) -> Peano.le y1 y0)).
Definition term115 (x0 : nat -> Prop) := (forall y0 : nat, (x0 y0) -> Peano.le y0 (NUMERAL 0)) /\ (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0)).
Definition term65 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, (x1 y0) -> Peano.le y0 x0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (forall y1 : nat, (x1 y1) -> Peano.le y1 y0)).
Definition term156 (x0 : nat) := @eq nat (S x0).
Definition term155 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (S x1))) -> (x0 (S x1)) = False.
Definition term99 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> x1 = (NUMERAL 0).
Definition term17 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term36 (x0 : Prop) (x1 : Prop) := @eq Prop ((True /\ x0) -> x1 /\ True).
Definition term39 (x0 : Prop) (x1 : Prop) := @eq Prop ((False /\ x0) -> x1 /\ False).
Definition term119 (x0 : nat -> Prop) := x0 (NUMERAL 0).
Definition term8 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term50 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (x0 y2) -> Peano.le y2 y1) y0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term70 (x0 : nat -> Prop) (x1 : nat) := ((forall y0 : nat, (x0 y0) -> Peano.le y0 x1) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> x0 x1.
Definition term159 (x0 : nat) := Peano.le (S x0) x0.
Definition term18 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term149 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x1) -> (x1 = (S x2)) \/ (Peano.le x1 x2).
Definition term64 (x0 : nat) (x1 : nat -> Prop) := ((fun y0 : nat => forall y1 : nat, (x1 y1) -> Peano.le y1 y0) x0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ ((fun y1 : nat => forall y2 : nat, (x1 y2) -> Peano.le y2 y1) y0)).
Definition term61 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) -> ~ (forall y1 : nat, (x1 y1) -> Peano.le y1 y0).
Definition term59 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) -> ~ (forall y0 : nat, (x1 y0) -> Peano.le y0 x2).
Definition term114 (x0 : Prop) := forall y0 : nat, x0.
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (S x1)).
Definition term140 (x0 : nat -> Prop) (x1 : nat) := x0 (S x1).
Definition term170 (x0 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (x0 y1) -> Peano.le y1 y0) -> exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term167 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term42 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)).
Definition term162 (x0 : nat) (x1 : nat) := (~ (x0 = (S x1))) -> (x0 = (S x1)) = False.
Definition term25 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 /\ x0) -> x1 /\ y0) = ((y0 /\ x0) -> x1)) True.
Definition term45 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => forall y2 : nat, (x0 y2) -> Peano.le y2 y1) y0.
Definition term78 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) x1.
Definition term137 (x0 : nat -> Prop) (x1 : nat) := True -> ~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1).
Definition term58 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) -> ~ ((fun y0 : nat => forall y1 : nat, (x1 y1) -> Peano.le y1 y0) x2).
Definition term158 (x0 : nat) := Peano.le (S x0).
Definition term107 (x0 : nat -> Prop) (x1 : nat) := (Peano.lt x1 (NUMERAL 0)) -> ~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1).
Definition term96 (x0 : nat -> Prop) := ((((forall y0 : nat, (x0 y0) -> Peano.le y0 (NUMERAL 0)) /\ (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> x0 (NUMERAL 0)) /\ (forall y0 : nat, (((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) -> ((forall y1 : nat, (x0 y1) -> Peano.le y1 (S y0)) /\ (forall y1 : nat, (Peano.lt y1 (S y0)) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 (S y0))) -> forall y0 : nat, ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0.
Definition term74 (x0 : nat -> Prop) := (fun y0 : nat => ((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) (NUMERAL 0).
Definition term154 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((x0 x1) -> (x1 = (S x2)) \/ (Peano.le x1 x2)) -> (x0 x1) -> Peano.le x1 x2.
Definition term21 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term34 (x0 : Prop) (x1 : Prop) := (False /\ x0) -> x1.
Definition term109 (x0 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term135 (x0 : nat) := True \/ (Peano.lt x0 x0).
Definition term24 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 /\ x0) -> x1 /\ y0) = ((y0 /\ x0) -> x1)) x2.
Definition term20 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term7 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term151 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := imp ((x0 x1) -> (x1 = (S x2)) \/ (Peano.le x1 x2)).
Definition term51 (x0 : nat -> Prop) := @eq Prop (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (x0 y2) -> Peano.le y2 y1) y0).
Definition term125 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((fun y0 : nat => x0 y0) x1).
Definition term164 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := imp ((x0 x1) -> Peano.le x1 x2).
Definition term129 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 (S x1)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0)) x1.
Definition term139 (x0 : nat -> Prop) (x1 : nat) := imp (~ (forall y0 : nat, (x0 y0) -> Peano.le y0 x1)).
Definition term2 (x0 : nat) (x1 : nat) := ~ (x0 = (S x1)).
Definition term28 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 /\ x0) -> x1 /\ y0) = ((y0 /\ x0) -> x1)) x2).
Definition term90 (x0 : nat -> Prop) := (((forall y0 : nat, (x0 y0) -> Peano.le y0 (NUMERAL 0)) /\ (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> ~ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0))) -> x0 (NUMERAL 0)) /\ (forall y0 : nat, (((forall y1 : nat, (x0 y1) -> Peano.le y1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 y0) -> ((forall y1 : nat, (x0 y1) -> Peano.le y1 (S y0)) /\ (forall y1 : nat, (Peano.lt y1 (S y0)) -> ~ (forall y2 : nat, (x0 y2) -> Peano.le y2 y1))) -> x0 (S y0)).
