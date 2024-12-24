Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term119 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)) -> exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x3 y1) y0).
Definition term29 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y3) (dest_nadd y1 y3))) y2)) x0.
Definition term25 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2))) x0.
Definition term46 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => (Peano.le (dest_nadd x1 y0) (Nat.add (dest_nadd x0 y0) x2)) /\ (Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)).
Definition term57 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := and (Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) x3)).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.le x0 x1).
Definition term44 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := (Peano.le (dest_nadd x1 x2) (Nat.add (dest_nadd x0 x2) x3)) /\ (Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) x3)).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term51 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, ((fun y1 : nat => Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) x2)) y0) /\ ((fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0).
Definition term32 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term28 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term72 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (exists y0 : nat, (forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x2 y1) y0))) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x2 y1) y0)).
Definition term77 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (dist (@pair nat nat y0 y1)) y2) = ((Peano.le y0 (Nat.add y1 y2)) /\ (Peano.le y1 (Nat.add y0 y2)))) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.le y0 y1)) x0.
Definition term34 (x0 : nadd) (x1 : nadd) := and (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0).
Definition term59 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => ((fun y1 : nat => Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) x2)) y0) /\ ((fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0).
Definition term101 (x0 : nadd) (x1 : nat) (x2 : nadd) := (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dest_nadd x0 y0) x1) y1) -> Peano.le (dest_nadd x2 y0) y1) -> forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dest_nadd x0 y0) x1) y1) -> Peano.le (dest_nadd x2 y0) y1.
Definition term88 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term53 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2).
Definition term41 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ ((nadd_eq x1 x3) /\ (nadd_le x0 x1))) -> nadd_le x2 x3.
Definition term124 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ ((nadd_eq y2 y3) /\ (nadd_le y0 y2))) -> nadd_le y1 y3.
Definition term123 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ ((nadd_eq y1 y2) /\ (nadd_le x0 y1))) -> nadd_le y0 y2.
Definition term122 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ ((nadd_eq y0 y1) /\ (nadd_le x0 y0))) -> nadd_le x1 y1.
Definition term52 (x0 : nadd) (x1 : nadd) (x2 : nat) := (forall y0 : nat, (fun y1 : nat => Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) x2)) y0) /\ (forall y0 : nat, (fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0).
Definition term48 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, (Peano.le (dest_nadd x1 y0) (Nat.add (dest_nadd x0 y0) x2)) /\ (Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)).
Definition term64 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x0 x2) (Nat.add x1 x2).
Definition term103 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (dest_nadd x0 x1) (Nat.add (Nat.add x2 x3) x4).
Definition term92 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd x0 x1) x2.
Definition term111 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.add (dest_nadd x0 x2) x5) (Nat.add (dest_nadd x1 x2) (Nat.add (Nat.add x3 x4) x5)).
Definition term63 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, (fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (dist (@pair nat nat x1 x0)) y0) = ((Peano.le x1 (Nat.add x0 y0)) /\ (Peano.le x0 (Nat.add x1 y0)))) x2.
Definition term102 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) (x6 : nat) := (Peano.le (Nat.add (dest_nadd x0 x3) x6) (Nat.add (dest_nadd x2 x3) (Nat.add (Nat.add x4 x5) x6))) -> Peano.le (dest_nadd x1 x3) (Nat.add (dest_nadd x2 x3) (Nat.add (Nat.add x4 x5) x6)).
Definition term109 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.add (Nat.add (dest_nadd x0 x1) x2) x3) x4.
Definition term49 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term69 (x0 : nadd) (x1 : nadd) := fun y0 : nat => (forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term54 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)) x3.
Definition term120 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((exists y0 : nat, (forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x3 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x3 y1) (Nat.add (dest_nadd x1 y1) y0))) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))) -> exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x3 y1) y0).
Definition term56 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := and ((fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)) x3).
Definition term86 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term45 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x1 y0))) x2.
Definition term75 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((exists y0 : nat, (forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x2 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x0 y1) y0))) /\ ((exists y0 : nat, (forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x3 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x3 y1) (Nat.add (dest_nadd x1 y1) y0))) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)))) -> exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x3 y1) y0).
Definition term42 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x2 y1))) y0) /\ ((exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 y1) (dest_nadd x3 y1))) y0) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)))) -> exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x3 y1) y0).
Definition term74 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := imp ((exists y0 : nat, (forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x2 y1) y0))) /\ ((exists y0 : nat, (forall y1 : nat, Peano.le (dest_nadd x3 y1) (Nat.add (dest_nadd x1 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x3 y1) y0))) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x3 y1) y0)))).
Definition term40 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := imp ((exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x2 y1) (dest_nadd x0 y1))) y0) /\ ((exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x3 y1) (dest_nadd x1 y1))) y0) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x3 y1) y0)))).
Definition term61 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq Prop (forall y0 : nat, (Peano.le (dest_nadd x1 y0) (Nat.add (dest_nadd x0 y0) x2)) /\ (Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2))).
Definition term60 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) x2)) y0) /\ ((fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0)).
Definition term9 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term105 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (dest_nadd x0 x1) (Nat.add x2 x3).
Definition term115 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.add (dest_nadd x0 x2) x4) (Nat.add (Nat.add (dest_nadd x1 x2) x3) x4).
Definition term104 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.add (dest_nadd x0 x1) (Nat.add x2 x3)) x4.
Definition term79 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (dist (@pair nat nat x0 y0)) y1) = ((Peano.le x0 (Nat.add y0 y1)) /\ (Peano.le y0 (Nat.add x0 y1)))) x1.
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1)) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.le x0 y0)) x1.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, (x0 y1) /\ (y0 y1)) = ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)).
Definition term118 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term39 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := imp ((nadd_eq x2 x0) /\ ((nadd_eq x3 x1) /\ (nadd_le x2 x3))).
Definition term98 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dest_nadd x0 x1) x2) x3.
Definition term21 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (dist (@pair nat nat x1 x0)) y0) = ((Peano.le x1 (Nat.add x0 y0)) /\ (Peano.le x0 (Nat.add x1 y0))).
Definition term107 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (dest_nadd x0 x1) (Nat.add x2 x3)).
Definition term80 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term31 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1)) x1.
Definition term27 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1))) x1.
Definition term66 (x0 : nadd) (x1 : nadd) (x2 : nat) := and (forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)).
Definition term108 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.add (dest_nadd x0 x1) x2) x3).
Definition term85 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term116 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) (Nat.add (Nat.add x3 x4) x5)).
Definition term95 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add (dest_nadd x0 y0) x1) y1) -> Peano.le (dest_nadd x2 y0) y1) x3.
Definition term94 (x0 : nadd) (x1 : nat) (x2 : nadd) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dest_nadd x0 y0) x1) y1) -> Peano.le (dest_nadd x2 y0) y1.
Definition term87 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term78 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term76 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term19 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (dist (@pair nat nat x0 y0)) y1) = ((Peano.le x0 (Nat.add y0 y1)) /\ (Peano.le y0 (Nat.add x0 y1))).
Definition term7 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.le x0 y0).
Definition term38 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x2 y1) (dest_nadd x0 y1))) y0) /\ ((exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x3 y1) (dest_nadd x1 y1))) y0) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x3 y1) y0))).
Definition term33 (x0 : nadd) (x1 : nadd) := and (nadd_eq x0 x1).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0) x2.
Definition term47 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x1 y0))) x2.
Definition term62 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => (fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (forall y2 : a0, (y0 y2) /\ (y1 y2)) = ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2))) x0.
Definition term58 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := ((fun y0 : nat => Peano.le (dest_nadd x1 y0) (Nat.add (dest_nadd x0 y0) x2)) x3) /\ ((fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)) x3).
Definition term70 (x0 : nadd) (x1 : nadd) := exists y0 : nat, (forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term99 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dest_nadd x0 x1) x2.
Definition term50 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term37 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x2 x0) /\ ((nadd_eq x3 x1) /\ (nadd_le x2 x3)).
Definition term96 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0) x4.
Definition term117 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) (Nat.add (Nat.add x2 x3) x4)).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term35 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq x2 x0) /\ (nadd_le x1 x2).
Definition term67 (x0 : nadd) (x1 : nadd) (x2 : nat) := (forall y0 : nat, Peano.le (dest_nadd x1 y0) (Nat.add (dest_nadd x0 y0) x2)) /\ (forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)).
Definition term68 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term100 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dest_nadd x0 y0) x1) y1) -> Peano.le (dest_nadd x2 y0) y1) -> Peano.le (dest_nadd x2 x3) x4.
Definition term106 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (dest_nadd x0 x1) x2) x3.
Definition term110 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (dest_nadd x0 x1) x2).
Definition term89 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term93 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := forall y0 : nat, (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0.
Definition term71 (x0 : nadd) (x1 : nadd) := and (exists y0 : nat, (forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))).
Definition term36 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x2 y1) (dest_nadd x0 y1))) y0) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x2 y1) y0)).
Definition term91 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.le (dest_nadd x2 x3) (Nat.add (dest_nadd x0 x3) x1)) -> forall y0 : nat, (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0)) x2.
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term121 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ ((nadd_eq x1 y0) /\ (nadd_le x0 x1))) -> nadd_le x2 y0.
Definition term55 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) x3).
Definition term65 (x0 : nadd) (x1 : nadd) (x2 : nat) := and (forall y0 : nat, (fun y1 : nat => Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) x2)) y0).
Definition term113 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (Nat.add (dest_nadd x1 x2) x3) x4).
Definition term43 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2))) x3.
Definition term30 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1).
Definition term26 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)).
Definition term112 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (Nat.add (dest_nadd x0 x2) x5) (Nat.add (Nat.add (Nat.add (dest_nadd x1 x2) x3) x4) x5).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term84 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 (Nat.add x0 x2)) /\ (Peano.le x0 (Nat.add x1 x2)).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.le x0 x1)) x2.
Definition term114 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := (Peano.le (Nat.add (dest_nadd x0 x3) x5) (Nat.add (Nat.add (dest_nadd x2 x3) x4) x5)) -> Peano.le (dest_nadd x1 x3) (Nat.add (Nat.add (dest_nadd x2 x3) x4) x5).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (x0 y1) /\ (y0 y1)) = ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1))) x1.
Definition term97 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dest_nadd x0 x3) x1) x4) -> Peano.le (dest_nadd x2 x3) x4.
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term73 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (exists y0 : nat, (forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x2 y1) y0))) /\ ((exists y0 : nat, (forall y1 : nat, Peano.le (dest_nadd x3 y1) (Nat.add (dest_nadd x1 y1) y0)) /\ (forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x3 y1) y0))) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x2 y1) (Nat.add (dest_nadd x3 y1) y0))).
