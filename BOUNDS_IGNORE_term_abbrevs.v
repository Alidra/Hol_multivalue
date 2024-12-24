Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term167 (x0 : nat -> nat) (x1 : nat -> nat) := (exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) (Nat.add (x1 y1) y0)) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y0).
Definition term166 (x0 : nat -> nat) (x1 : nat -> nat) := (exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y0)) -> exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) (Nat.add (x1 y1) y0).
Definition term121 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := (exists y0 : nat, forall y1 : nat, (Peano.le x0 y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0)) -> exists y0 : nat, forall y1 : nat, Peano.le (x1 y1) (Nat.add (x2 y1) y0).
Definition term40 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term103 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := True -> Peano.le (x0 x2) (Nat.add (x1 x2) x3).
Definition term73 (x0 : nat -> nat) (x1 : nat -> nat) := fun y0 : nat => exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y0).
Definition term16 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term18 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term119 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := exists y0 : nat, forall y1 : nat, (Peano.le x0 y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0).
Definition term57 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (x0 y1) (Nat.add (x1 y1) x2).
Definition term54 (x0 : nat -> nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) (Nat.add (x1 y1) y0).
Definition term163 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := forall y0 : nat, (Peano.le x3 y0) -> Peano.le (x2 y0) (Nat.add (x0 y0) (Nat.add x1 (x2 x3))).
Definition term32 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) x0.
Definition term132 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (Peano.le (x0 x2) (Nat.add (x1 x2) x3)) /\ True.
Definition term105 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => Peano.le (x0 y0) (Nat.add (x1 y0) x2).
Definition term153 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Peano.le (x2 x3) (Nat.add (x0 x3) (Nat.add x1 (x2 x3))).
Definition term142 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := (~ (Peano.le (S x4) x1)) -> Peano.le (x3 x1) (Nat.add (x0 x1) (Nat.add x2 (x3 x4))).
Definition term15 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term139 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := Peano.le (x3 x1) (Nat.add (x0 x1) (Nat.add x2 (x3 x4))).
Definition term45 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term67 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term159 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Peano.le (x2 x3) (Nat.add (Nat.add (x0 x3) x1) (x2 x3)).
Definition term48 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (Peano.le (S x0) x1).
Definition term143 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := ((x1 = x4) \/ (Peano.lt x1 x4)) -> Peano.le (x3 x1) (Nat.add (x0 x1) (Nat.add x2 (x3 x4))).
Definition term92 (x0 : nat -> nat) (x1 : nat -> nat) := forall y0 : nat, (forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> forall y1 : nat, (forall y2 : nat, (Peano.le (S y0) y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2).
Definition term85 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) (S x2).
Definition term124 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := Nat.add (x0 x1) (Nat.add x2 (x3 x4)).
Definition term100 (x0 : nat -> nat) (x1 : nat -> nat) := ((forall y0 : nat, (forall y1 : nat, (Peano.le (NUMERAL 0) y1) -> Peano.le (x0 y1) (Nat.add (x1 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (x1 y2) y1)) /\ (forall y0 : nat, (forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> forall y1 : nat, (forall y2 : nat, (Peano.le (S y0) y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2))) -> forall y0 : nat, forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2).
Definition term50 (x0 : nat) (x1 : nat) := (Peano.le (S x0) x1) \/ (~ (Peano.le (S x0) x1)).
Definition term39 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term43 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term104 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => (Peano.le (NUMERAL 0) y0) -> Peano.le (x0 y0) (Nat.add (x1 y0) x2).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term52 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term127 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := Peano.le (Nat.add (x0 x1) x2) (Nat.add (x0 x1) (Nat.add x2 (x3 x4))).
Definition term61 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term75 (x0 : nat -> nat) (x1 : nat -> nat) := (((fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) y0) -> (fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) y0.
Definition term164 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add x0 (x1 x2).
Definition term87 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) x2) -> (fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) (S x2).
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term74 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term134 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := (Peano.le (S x0) x3) -> Peano.le (x1 x3) (Nat.add (x2 x3) x4).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term95 (x0 : nat -> nat) (x1 : nat -> nat) := imp (((fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) y0) -> (fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) (S y0))).
Definition term10 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term55 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := forall y0 : nat, Peano.le (x0 y0) (Nat.add (x1 y0) x2).
Definition term70 := exists y0 : nat, True.
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1)) x1.
Definition term91 (x0 : nat -> nat) (x1 : nat -> nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) y0) -> (fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) (S y0).
Definition term140 (x0 : nat) (x1 : nat) := imp (~ (Peano.le (S x0) x1)).
Definition term114 (x0 : nat -> nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (x0 y1) (Nat.add (x1 y1) y0).
Definition term19 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term28 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term125 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := Nat.add (Nat.add (x0 x1) x2) (x3 x4).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term165 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat -> nat) := (forall y0 : nat, (Peano.le (S x0) y0) -> Peano.le (x2 y0) (Nat.add (x3 y0) x1)) -> exists y0 : nat, forall y1 : nat, Peano.le (x2 y1) (Nat.add (x3 y1) y0).
Definition term118 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := (forall y0 : nat, (forall y1 : nat, (Peano.le x0 y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x1 y2) (Nat.add (x2 y2) y1)) -> exists y0 : nat, forall y1 : nat, Peano.le (x1 y1) (Nat.add (x2 y1) y0).
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat -> nat) := (forall y0 : nat, (Peano.le x0 y0) -> Peano.le (x2 y0) (Nat.add (x3 y0) x1)) -> exists y0 : nat, forall y1 : nat, Peano.le (x2 y1) (Nat.add (x3 y1) y0).
Definition term110 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := (forall y0 : nat, Peano.le (x1 y0) (Nat.add (x2 y0) x0)) -> exists y0 : nat, forall y1 : nat, Peano.le (x1 y1) (Nat.add (x2 y1) y0).
Definition term109 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := (forall y0 : nat, (Peano.le (NUMERAL 0) y0) -> Peano.le (x1 y0) (Nat.add (x2 y0) x0)) -> exists y0 : nat, forall y1 : nat, Peano.le (x1 y1) (Nat.add (x2 y1) y0).
Definition term150 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := fun y0 : nat => Peano.le (x2 y0) (Nat.add (x0 y0) (Nat.add x1 (x2 x3))).
Definition term160 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Nat.add (x0 x2) (Nat.add (x1 x2) x3).
Definition term112 (x0 : nat -> nat) (x1 : nat -> nat) := fun y0 : nat => (forall y1 : nat, Peano.le (x0 y1) (Nat.add (x1 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (x1 y2) y1).
Definition term111 (x0 : nat -> nat) (x1 : nat -> nat) := fun y0 : nat => (forall y1 : nat, (Peano.le (NUMERAL 0) y1) -> Peano.le (x0 y1) (Nat.add (x1 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (x1 y2) y1).
Definition term14 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term168 (x0 : nat -> nat) (x1 : nat -> nat) := ((exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) (Nat.add (x1 y1) y0)) -> exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y0)) /\ ((exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y0)) -> exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) (Nat.add (x1 y1) y0)).
Definition term115 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) (x3 : nat) := forall y0 : nat, (Peano.le (S x0) y0) -> Peano.le (x1 y0) (Nat.add (x2 y0) x3).
Definition term106 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := forall y0 : nat, (Peano.le (NUMERAL 0) y0) -> Peano.le (x0 y0) (Nat.add (x1 y0) x2).
Definition term58 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) (x3 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le (x1 y0) (Nat.add (x2 y0) x3).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term79 (x0 : nat -> nat) (x1 : nat -> nat) := and ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) (NUMERAL 0)).
Definition term108 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := imp (forall y0 : nat, Peano.le (x0 y0) (Nat.add (x1 y0) x2)).
Definition term107 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := imp (forall y0 : nat, (Peano.le (NUMERAL 0) y0) -> Peano.le (x0 y0) (Nat.add (x1 y0) x2)).
Definition term84 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := imp (forall y0 : nat, (forall y1 : nat, (Peano.le x0 y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x1 y2) (Nat.add (x2 y2) y1)).
Definition term80 (x0 : nat -> nat) (x1 : nat -> nat) := and (forall y0 : nat, (forall y1 : nat, (Peano.le (NUMERAL 0) y1) -> Peano.le (x0 y1) (Nat.add (x1 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (x1 y2) y1)).
Definition term72 (x0 : Prop) := exists y0 : nat, x0.
Definition term77 (x0 : nat -> nat) (x1 : nat -> nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) (NUMERAL 0).
Definition term148 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term155 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := @eq Prop (Peano.le (x3 x1) (Nat.add (x0 x1) (Nat.add x2 (x3 x4)))).
Definition term96 (x0 : nat -> nat) (x1 : nat -> nat) := imp ((forall y0 : nat, (forall y1 : nat, (Peano.le (NUMERAL 0) y1) -> Peano.le (x0 y1) (Nat.add (x1 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (x1 y2) y1)) /\ (forall y0 : nat, (forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> forall y1 : nat, (forall y2 : nat, (Peano.le (S y0) y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2))).
Definition term156 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add (x0 x3) (Nat.add x1 (x2 x3)).
Definition term131 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := (Peano.le (x3 x1) (Nat.add (x0 x1) x2)) /\ (Peano.le (Nat.add (x0 x1) x2) (Nat.add (x0 x1) (Nat.add x2 (x3 x4)))).
Definition term113 (x0 : nat -> nat) (x1 : nat -> nat) := forall y0 : nat, (forall y1 : nat, Peano.le (x0 y1) (Nat.add (x1 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (x1 y2) y1).
Definition term86 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := forall y0 : nat, (forall y1 : nat, (Peano.le (S x0) y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x1 y2) (Nat.add (x2 y2) y1).
Definition term82 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := forall y0 : nat, (forall y1 : nat, (Peano.le x0 y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x1 y2) (Nat.add (x2 y2) y1).
Definition term78 (x0 : nat -> nat) (x1 : nat -> nat) := forall y0 : nat, (forall y1 : nat, (Peano.le (NUMERAL 0) y1) -> Peano.le (x0 y1) (Nat.add (x1 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (x1 y2) y1).
Definition term99 (x0 : nat -> nat) (x1 : nat -> nat) := forall y0 : nat, forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2).
Definition term44 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term33 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term31 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term23 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term22 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term21 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term81 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) x2.
Definition term17 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term141 (x0 : nat) (x1 : nat) := imp ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term76 (x0 : nat -> nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2).
Definition term27 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term66 := forall y0 : nat, True.
Definition term154 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := @eq Prop ((fun y0 : nat => Peano.le (x2 y0) (Nat.add (x0 y0) (Nat.add x1 (x2 x3)))) x4).
Definition term162 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := (Peano.le x4 x1) -> Peano.le (x3 x1) (Nat.add (x0 x1) (Nat.add x2 (x3 x4))).
Definition term126 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (x0 x1) x2).
Definition term53 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term65 := fun y0 : nat => True.
Definition term25 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term149 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := (x1 = x4) -> Peano.le (x3 x1) (Nat.add (x0 x1) (Nat.add x2 (x3 x4))).
Definition term116 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) (x3 : nat) := (fun y0 : nat => (forall y1 : nat, (Peano.le x0 y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x1 y2) (Nat.add (x2 y2) y1)) x3.
Definition term5 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term135 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := (forall y0 : nat, (Peano.le (S x0) y0) -> Peano.le (x1 y0) (Nat.add (x2 y0) x4)) -> Peano.le (x1 x3) (Nat.add (x2 x3) x4).
Definition term130 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := and (Peano.le (x0 x2) (Nat.add (x1 x2) x3)).
Definition term90 (x0 : nat -> nat) (x1 : nat -> nat) := fun y0 : nat => (forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> forall y1 : nat, (forall y2 : nat, (Peano.le (S y0) y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2).
Definition term89 (x0 : nat -> nat) (x1 : nat -> nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) y0) -> (fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) (S y0).
Definition term63 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> True.
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term137 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := exists y0 : nat, (Peano.le (x3 x1) y0) /\ (Peano.le y0 (Nat.add (x0 x1) (Nat.add x2 (x3 x4)))).
Definition term71 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term35 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term129 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (x0 x1) x2.
Definition term26 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term128 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := Peano.le (Nat.add (x0 x1) x2) (Nat.add (Nat.add (x0 x1) x2) (x3 x4)).
Definition term83 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := imp ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) x2).
Definition term94 (x0 : nat -> nat) (x1 : nat -> nat) := (forall y0 : nat, (forall y1 : nat, (Peano.le (NUMERAL 0) y1) -> Peano.le (x0 y1) (Nat.add (x1 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (x1 y2) y1)) /\ (forall y0 : nat, (forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> forall y1 : nat, (forall y2 : nat, (Peano.le (S y0) y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)).
Definition term51 (x0 : nat) (x1 : nat) := ~ (Peano.le (S x0) x1).
Definition term170 := forall y0 : nat -> nat, forall y1 : nat -> nat, (exists y2 : nat, forall y3 : nat, Peano.le (y0 y3) (Nat.add (y1 y3) y2)) = (exists y2 : nat, exists y3 : nat, forall y4 : nat, (Peano.le y3 y4) -> Peano.le (y0 y4) (Nat.add (y1 y4) y2)).
Definition term97 (x0 : nat -> nat) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) y0.
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term144 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term29 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term59 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (x0 y0) (Nat.add (x1 y0) x2)) x3.
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term157 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add (Nat.add (x0 x3) x1) (x2 x3).
Definition term138 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := fun y0 : nat => (Peano.le (x3 x1) y0) /\ (Peano.le y0 (Nat.add (x0 x1) (Nat.add x2 (x3 x4)))).
Definition term93 (x0 : nat -> nat) (x1 : nat -> nat) := ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, (Peano.le y0 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y1)) -> exists y2 : nat, forall y3 : nat, Peano.le (x0 y3) (Nat.add (x1 y3) y2)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) y0) -> (fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) (S y0)).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0)) x2.
Definition term169 (x0 : nat -> nat) := forall y0 : nat -> nat, (exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (y0 y2) y1)) = (exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le (x0 y3) (Nat.add (y0 y3) y1)).
Definition term49 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term64 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) (x3 : nat) := fun y0 : nat => (Peano.le x0 y0) -> Peano.le (x1 y0) (Nat.add (x2 y0) x3).
Definition term145 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term42 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term158 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 x1).
Definition term101 (x0 : nat) := imp (Peano.le (NUMERAL 0) x0).
Definition term102 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (Peano.le (NUMERAL 0) x2) -> Peano.le (x0 x2) (Nat.add (x1 x2) x3).
Definition term147 (x0 : nat) (x1 : nat) := (x0 = x1) \/ False.
Definition term152 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := (fun y0 : nat => Peano.le (x2 y0) (Nat.add (x0 y0) (Nat.add x1 (x2 x3)))) x3.
Definition term123 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) (x4 : nat) := (exists y0 : nat, (Peano.le (x3 x1) y0) /\ (Peano.le y0 (Nat.add (x0 x1) (Nat.add x2 (x3 x4))))) -> Peano.le (x3 x1) (Nat.add (x0 x1) (Nat.add x2 (x3 x4))).
Definition term68 (x0 : Prop) := forall y0 : nat, x0.
Definition term41 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term20 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term56 (x0 : nat -> nat) (x1 : nat -> nat) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y0).
Definition term133 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) -> Peano.le (x1 y0) (Nat.add (x2 y0) x3)) x4.
Definition term60 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Peano.le (x0 x2) (Nat.add (x1 x2) x3).
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term161 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Peano.le (x0 x2) (Nat.add (x0 x2) (Nat.add (x1 x2) x3)).
Definition term151 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => Peano.le (x2 y0) (Nat.add (x0 y0) (Nat.add x1 (x2 x3)))) x4.
Definition term98 (x0 : nat -> nat) (x1 : nat -> nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (forall y3 : nat, (Peano.le y1 y3) -> Peano.le (x0 y3) (Nat.add (x1 y3) y2)) -> exists y3 : nat, forall y4 : nat, Peano.le (x0 y4) (Nat.add (x1 y4) y3)) y0.
Definition term122 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := (forall y0 : nat, (forall y1 : nat, (Peano.le x0 y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x1 y2) (Nat.add (x2 y2) y1)) -> (exists y0 : nat, forall y1 : nat, (Peano.le x0 y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0)) -> exists y0 : nat, forall y1 : nat, Peano.le (x1 y1) (Nat.add (x2 y1) y0).
Definition term62 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := (Peano.le x0 x3) -> Peano.le (x1 x3) (Nat.add (x2 x3) x4).
Definition term146 (x0 : nat) (x1 : nat) := or (x0 = x1).
Definition term120 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := fun y0 : nat => forall y1 : nat, (Peano.le x0 y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0).
Definition term69 (x0 : nat -> nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le (x0 y1) (Nat.add (x1 y1) x2).
Definition term47 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term136 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) (x3 : nat) := (forall y0 : nat, (Peano.le (S x0) y0) -> Peano.le (x1 y0) (Nat.add (x2 y0) x3)) -> forall y0 : nat, (Peano.le (S x0) y0) -> Peano.le (x1 y0) (Nat.add (x2 y0) x3).
Definition term88 (x0 : nat) (x1 : nat -> nat) (x2 : nat -> nat) := (forall y0 : nat, (forall y1 : nat, (Peano.le x0 y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x1 y2) (Nat.add (x2 y2) y1)) -> forall y0 : nat, (forall y1 : nat, (Peano.le (S x0) y1) -> Peano.le (x1 y1) (Nat.add (x2 y1) y0)) -> exists y1 : nat, forall y2 : nat, Peano.le (x1 y2) (Nat.add (x2 y2) y1).
