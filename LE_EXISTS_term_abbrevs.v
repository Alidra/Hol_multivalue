Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term197 (x0 : nat) (x1 : nat) := (((x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))) -> exists y0 : nat, (S x0) = (Nat.add x1 y0)) /\ ((exists y0 : nat, (S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term108 := exists y0 : nat, y0 = (NUMERAL 0).
Definition term80 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term140 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, (fun y1 : nat => (S x0) = (Nat.add x1 y1)) y0).
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term3 (a0 : Type') (x0 : a0) := exists y0 : a0, x0 = y0.
Definition term153 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) (NUMERAL 0).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term102 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ ((fun y0 : nat => y0 = (NUMERAL 0)) x1).
Definition term184 (x0 : nat) (x1 : nat) := (x1 = x1) \/ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term61 (x0 : nat) (x1 : nat) := imp ((Peano.le x1 x0) = (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term55 (x0 : nat) := exists y0 : nat, (NUMERAL 0) = (Nat.add x0 y0).
Definition term129 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term191 (x0 : nat) := or (x0 = x0).
Definition term88 (x0 : nat) (x1 : nat) := or (x0 = (S x1)).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((S x0) = (Nat.add x1 x2)).
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = (Nat.add x2 x0)) -> (x2 = (S x1)) \/ (exists y0 : nat, x1 = (Nat.add x2 y0)).
Definition term94 (x0 : nat) := exists y0 : nat, (x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)).
Definition term130 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.add x1 y0)) -> exists y0 : nat, (S x0) = (Nat.add x1 y0).
Definition term42 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term192 (x0 : nat) (x1 : nat) := True \/ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term18 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term97 (x0 : nat) := exists y0 : nat, (x0 = (NUMERAL 0)) /\ ((fun y1 : nat => y1 = (NUMERAL 0)) y0).
Definition term103 (x0 : nat) := fun y0 : nat => (x0 = (NUMERAL 0)) /\ ((fun y1 : nat => y1 = (NUMERAL 0)) y0).
Definition term175 (x0 : nat) (x1 : nat) := imp ((S x0) = (Nat.add x1 (NUMERAL 0))).
Definition term179 (x0 : nat) (x1 : nat) (x2 : nat) := imp (x0 = (Nat.add x1 x2)).
Definition term15 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term12 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term173 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) y0.
Definition term76 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) y0.
Definition term150 (x0 : nat) (x1 : nat) := fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1)).
Definition term168 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) y0) -> (fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) (S y0)).
Definition term71 (x0 : nat) := ((fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) y0) -> (fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) (S y0)).
Definition term77 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term176 (x0 : nat) (x1 : nat) := imp ((S x0) = x1).
Definition term74 (x0 : nat) := imp (((Peano.le x0 (NUMERAL 0)) = (exists y0 : nat, (NUMERAL 0) = (Nat.add x0 y0))) /\ (forall y0 : nat, ((Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) -> (Peano.le x0 (S y0)) = (exists y1 : nat, (S y0) = (Nat.add x0 y1)))).
Definition term189 (x0 : nat) (x1 : nat) := (x1 = (S (Nat.add x1 x0))) \/ (exists y0 : nat, (Nat.add x1 x0) = (Nat.add x1 y0)).
Definition term196 (x0 : nat) := exists y0 : nat, x0 = y0.
Definition term125 (x0 : nat) (x1 : nat) := exists y0 : nat, (S (Nat.add x1 x0)) = (Nat.add x1 y0).
Definition term26 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term5 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y0 = y1.
Definition term43 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term41 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0, x0 /\ (y0 y1)) = (x0 /\ (exists y1 : a0, y0 y1))) x1.
Definition term190 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (x0 = (S y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))) x1).
Definition term78 (x0 : nat) := (((Peano.le x0 (NUMERAL 0)) = (exists y0 : nat, (NUMERAL 0) = (Nat.add x0 y0))) /\ (forall y0 : nat, ((Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) -> (Peano.le x0 (S y0)) = (exists y1 : nat, (S y0) = (Nat.add x0 y1)))) -> forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term65 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1) -> (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) (S x1).
Definition term101 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term152 (x0 : nat) (x1 : nat) := (((fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) y0) -> (fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) (S y0))) -> forall y0 : nat, (fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) y0.
Definition term51 (x0 : nat) := (((fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) y0) -> (fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) y0.
Definition term38 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y1 = y0) x0.
Definition term149 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (S x0) = (Nat.add x1 y1)) y0) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1)).
Definition term134 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (S x0) = (Nat.add x1 y1)) y0) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term50 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term7 (a0 : Type') := forall y0 : a0, exists y1 : a0, y0 = y1.
Definition term6 (a0 : Type') := forall y0 : a0, exists y1 : a0, y1 = y0.
Definition term35 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term8 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y0 = y1) x0.
Definition term141 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, (S x0) = (Nat.add x1 y0)).
Definition term170 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) y0) -> (fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) (S y0))).
Definition term73 (x0 : nat) := imp (((fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) y0) -> (fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) (S y0))).
Definition term122 (x0 : nat) := fun y0 : nat => exists y1 : nat, (S y0) = (Nat.add x0 y1).
Definition term112 (x0 : nat) := fun y0 : nat => exists y1 : nat, (S x0) = (Nat.add y0 y1).
Definition term27 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term45 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term194 (x0 : nat) := fun y0 : nat => x0 = y0.
Definition term186 (x0 : nat) := fun y0 : nat => (x0 = (S y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term72 (x0 : nat) := ((Peano.le x0 (NUMERAL 0)) = (exists y0 : nat, (NUMERAL 0) = (Nat.add x0 y0))) /\ (forall y0 : nat, ((Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) -> (Peano.le x0 (S y0)) = (exists y1 : nat, (S y0) = (Nat.add x0 y1))).
Definition term81 (x0 : nat) := @eq Prop (Peano.le x0 (NUMERAL 0)).
Definition term166 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) y0) -> (fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) (S y0).
Definition term69 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) y0) -> (fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) (S y0).
Definition term47 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term39 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (exists y2 : a0, y0 /\ (y1 y2)) = (y0 /\ (exists y2 : a0, y1 y2))) x0.
Definition term40 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (exists y1 : a0, x0 /\ (y0 y1)) = (x0 /\ (exists y1 : a0, y0 y1)).
Definition term117 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, (S x0) = (Nat.add x1 y0)).
Definition term105 (x0 : nat) := @eq Prop (exists y0 : nat, (x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term104 (x0 : nat) := @eq Prop (exists y0 : nat, (x0 = (NUMERAL 0)) /\ ((fun y1 : nat => y1 = (NUMERAL 0)) y0)).
Definition term126 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => exists y1 : nat, (S y0) = (Nat.add x0 y1)) x1).
Definition term116 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => exists y1 : nat, (S x0) = (Nat.add y0 y1)) x1).
Definition term95 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term25 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term188 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = (S y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))) (Nat.add x0 x1).
Definition term92 (x0 : nat) := fun y0 : nat => (NUMERAL 0) = (Nat.add x0 y0).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := ((S x1) = (Nat.add x2 x0)) -> (x2 = (S x1)) \/ (exists y0 : nat, x1 = (Nat.add x2 y0)).
Definition term48 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.add x0 x1) = (NUMERAL 0)).
Definition term178 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((S x0) = (Nat.add x1 (S x2))).
Definition term155 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) (NUMERAL 0)).
Definition term56 (x0 : nat) := and ((fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) (NUMERAL 0)).
Definition term96 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (S x0) = (Nat.add x1 y0)) x2.
Definition term182 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) \/ (exists y1 : nat, x1 = (Nat.add x0 y1))) (S x1).
Definition term36 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term164 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) y0) -> (fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) (S y0).
Definition term67 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) y0) -> (fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) (S y0).
Definition term111 (x0 : nat) := (x0 = (NUMERAL 0)) /\ True.
Definition term193 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x1 x0) = (Nat.add x1 y0).
Definition term59 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0)) x1.
Definition term172 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((S x0) = (Nat.add x1 y1)) -> (x1 = (S x0)) \/ (exists y2 : nat, x0 = (Nat.add x1 y2))) y0.
Definition term98 (x0 : nat) := (x0 = (NUMERAL 0)) /\ (exists y0 : nat, (fun y1 : nat => y1 = (NUMERAL 0)) y0).
Definition term136 (x0 : nat) (x1 : nat) := fun y0 : nat => (S x0) = (Nat.add x1 y0).
Definition term165 (x0 : nat) (x1 : nat) := fun y0 : nat => (((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) -> ((S x0) = (Nat.add x1 (S y0))) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1)).
Definition term24 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term123 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (S y0) = (Nat.add x0 y1)) x1.
Definition term113 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (S x0) = (Nat.add y0 y1)) x1.
Definition term198 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2)).
Definition term83 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term33 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term19 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term10 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) (S x2).
Definition term174 (x0 : nat) (x1 : nat) := ((((S x0) = (Nat.add x1 (NUMERAL 0))) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))) /\ (forall y0 : nat, (((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) -> ((S x0) = (Nat.add x1 (S y0))) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1)))) -> forall y0 : nat, ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1)).
Definition term169 (x0 : nat) (x1 : nat) := (((S x0) = (Nat.add x1 (NUMERAL 0))) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))) /\ (forall y0 : nat, (((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) -> ((S x0) = (Nat.add x1 (S y0))) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))).
Definition term90 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 (S x1)).
Definition term132 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) -> x1.
Definition term60 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((exists y2 : a0, y0 y2) -> y1) = (forall y2 : a0, (y0 y2) -> y1)) x0.
Definition term85 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term109 (x0 : nat) := (x0 = (NUMERAL 0)) /\ (exists y0 : nat, y0 = (NUMERAL 0)).
Definition term154 (x0 : nat) (x1 : nat) := ((S x0) = (Nat.add x1 (NUMERAL 0))) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term133 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) -> x1.
Definition term53 (x0 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) (NUMERAL 0).
Definition term131 (x0 : nat) (x1 : nat) := ((x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))) -> exists y0 : nat, (S x0) = (Nat.add x1 y0).
Definition term110 (x0 : nat) := exists y0 : nat, y0 = x0.
Definition term2 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term4 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y1 = y0.
Definition term115 (x0 : nat) := exists y0 : nat, (S x0) = (Nat.add (S x0) y0).
Definition term121 (x0 : nat) := fun y0 : nat => (S x0) = (Nat.add (S x0) y0).
Definition term139 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (S x0) = (Nat.add x1 y1)) y0.
Definition term107 := exists y0 : nat, (fun y1 : nat => y1 = (NUMERAL 0)) y0.
Definition term91 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term64 (x0 : nat) (x1 : nat) := exists y0 : nat, (S x0) = (Nat.add x1 y0).
Definition term0 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term17 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term135 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (S x0) = (Nat.add x1 y1)) y0) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1)).
Definition term100 (x0 : nat) := (fun y0 : nat => y0 = (NUMERAL 0)) x0.
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) := (((S x1) = (Nat.add x2 x0)) -> (x2 = (S x1)) \/ (exists y0 : nat, x1 = (Nat.add x2 y0))) -> ((S x1) = (Nat.add x2 (S x0))) -> (x2 = (S x1)) \/ (exists y0 : nat, x1 = (Nat.add x2 y0)).
Definition term120 (x0 : nat) := @eq nat (S x0).
Definition term183 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x1 = y0) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) x1.
Definition term177 (x0 : nat) (x1 : nat) := ((S x0) = x1) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0).
Definition term87 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (S x1) = (Nat.add x2 y0)) x0) -> (x2 = (S x1)) \/ (exists y0 : nat, x1 = (Nat.add x2 y0)).
Definition term84 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term44 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0.
Definition term34 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term127 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add x0 x1)).
Definition term75 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 y1) = (exists y2 : nat, y1 = (Nat.add x0 y2))) y0.
Definition term187 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = (S y0)) \/ (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term119 (x0 : nat) := S (Nat.add x0 (NUMERAL 0)).
Definition term106 := fun y0 : nat => (fun y1 : nat => y1 = (NUMERAL 0)) y0.
Definition term195 (x0 : nat) (x1 : nat) := exists y0 : nat, (Nat.add x1 x0) = (Nat.add x1 y0).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term79 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term23 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term57 (x0 : nat) := and ((Peano.le x0 (NUMERAL 0)) = (exists y0 : nat, (NUMERAL 0) = (Nat.add x0 y0))).
Definition term114 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (S x0) = (Nat.add y0 y1)) (S x0).
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat) := imp (((S x1) = (Nat.add x2 x0)) -> (x2 = (S x1)) \/ (exists y0 : nat, x1 = (Nat.add x2 y0))).
Definition term62 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) (S x1).
Definition term49 (x0 : nat) (x1 : nat) := @eq Prop ((NUMERAL 0) = (Nat.add x0 x1)).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term171 (x0 : nat) (x1 : nat) := imp ((((S x0) = (Nat.add x1 (NUMERAL 0))) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))) /\ (forall y0 : nat, (((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) -> ((S x0) = (Nat.add x1 (S y0))) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1)))).
Definition term68 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) -> (Peano.le x0 (S y0)) = (exists y1 : nat, (S y0) = (Nat.add x0 y1)).
Definition term138 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (S x0) = (Nat.add x1 y1)) y0.
Definition term128 (x0 : nat) (x1 : nat) := fun y0 : nat => (S (Nat.add x1 x0)) = (Nat.add x1 y0).
Definition term99 := fun y0 : nat => y0 = (NUMERAL 0).
Definition term167 (x0 : nat) (x1 : nat) := forall y0 : nat, (((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) -> ((S x0) = (Nat.add x1 (S y0))) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1)).
Definition term124 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (S y0) = (Nat.add x0 y1)) (Nat.add x0 x1).
Definition term162 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) x2) -> (fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) (S x2).
Definition term1 (a0 : Type') (x0 : a0) := fun y0 : a0 => x0 = y0.
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) x2.
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1))) x2).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => (S x0) = (Nat.add x1 y0)) x2).
Definition term58 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term66 (x0 : nat) (x1 : nat) := ((Peano.le x1 x0) = (exists y0 : nat, x0 = (Nat.add x1 y0))) -> (Peano.le x1 (S x0)) = (exists y0 : nat, (S x0) = (Nat.add x1 y0)).
Definition term181 (x0 : nat) (x1 : nat) := fun y0 : nat => (x1 = y0) \/ (exists y1 : nat, x0 = (Nat.add x1 y1)).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term54 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term86 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term63 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term52 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term156 (x0 : nat) (x1 : nat) := and (((S x0) = (Nat.add x1 (NUMERAL 0))) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term93 (x0 : nat) := fun y0 : nat => (x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)).
Definition term89 (x0 : nat) (x1 : nat) := (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term142 (x0 : nat) (x1 : nat) := (exists y0 : nat, (S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term118 (x0 : nat) := Nat.add (S x0) (NUMERAL 0).
Definition term151 (x0 : nat) (x1 : nat) := forall y0 : nat, ((S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y1 : nat, x0 = (Nat.add x1 y1)).
Definition term70 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) -> (Peano.le x0 (S y0)) = (exists y1 : nat, (S y0) = (Nat.add x0 y1)).
Definition term37 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term82 (x0 : nat) := @eq Prop (x0 = (NUMERAL 0)).
Definition term144 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (S x0) = (Nat.add x1 y0)) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term143 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (S x0) = (Nat.add x1 y1)) y0) -> (x1 = (S x0)) \/ (exists y0 : nat, x0 = (Nat.add x1 y0))).
Definition term185 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (x0 = y0) \/ (exists y1 : nat, x1 = (Nat.add x0 y1))) (S x1)).
Definition term161 (x0 : nat) (x1 : nat) (x2 : nat) := ((S x1) = (Nat.add x2 (S x0))) -> (x2 = (S x1)) \/ (exists y0 : nat, x1 = (Nat.add x2 y0)).
Definition term46 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1.
Definition term21 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).