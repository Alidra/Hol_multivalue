Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term91 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Peano.le (dest_nadd x1 y0) (Nat.add (dest_nadd x0 y0) x2)) /\ (Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2))) x3.
Definition term11 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2))) x0.
Definition term7 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y3) (dest_nadd y1 y3))) y2)) x0.
Definition term61 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dest_nadd x1 x2) x4) (Nat.add (dest_nadd x1 x2) (Nat.add x3 x4))) -> Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) (Nat.add x3 x4)).
Definition term59 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dest_nadd x1 x2) x3) (Nat.add (dest_nadd x1 x2) (Nat.add x3 x4))) -> Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) (Nat.add x3 x4)).
Definition term24 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => (Peano.le (dest_nadd x1 y0) (Nat.add (dest_nadd x0 y0) x2)) /\ (Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)).
Definition term80 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.le x0 x1).
Definition term22 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := (Peano.le (dest_nadd x1 x2) (Nat.add (dest_nadd x0 x2) x3)) /\ (Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) x3)).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term29 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, (Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term14 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term10 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term85 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dest_nadd x0 x1) (Nat.add (dest_nadd x0 x1) x2).
Definition term77 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.le y0 y1)) x0.
Definition term66 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) x0.
Definition term34 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (dist (@pair nat nat y0 y1)) y2) = ((Peano.le y0 (Nat.add y1 y2)) /\ (Peano.le y1 (Nat.add y0 y2)))) x0.
Definition term98 (x0 : nadd) (x1 : nadd) := (((exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))) -> exists y0 : nat, forall y1 : nat, (Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))) /\ ((exists y0 : nat, forall y1 : nat, (Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))) -> (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))).
Definition term16 (x0 : nadd) (x1 : nadd) := and (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term58 (x0 : nadd) (x1 : nat) (x2 : nadd) := (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dest_nadd x0 y0) x1) y1) -> Peano.le (dest_nadd x2 y0) y1) -> forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dest_nadd x0 y0) x1) y1) -> Peano.le (dest_nadd x2 y0) y1.
Definition term45 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term95 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term76 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dest_nadd x0 x1) x2) (Nat.add (Nat.add (dest_nadd x0 x1) x2) x3).
Definition term92 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2).
Definition term100 := forall y0 : nadd, forall y1 : nadd, ((nadd_le y0 y1) /\ (nadd_le y1 y0)) = (nadd_eq y0 y1).
Definition term26 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, (Peano.le (dest_nadd x1 y0) (Nat.add (dest_nadd x0 y0) x2)) /\ (Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)).
Definition term30 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x0 x2) (Nat.add x1 x2).
Definition term49 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd x0 x1) x2.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (dist (@pair nat nat x1 x0)) y0) = ((Peano.le x1 (Nat.add x0 y0)) /\ (Peano.le x0 (Nat.add x1 y0)))) x2.
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term31 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) x2)) x3.
Definition term90 (x0 : nadd) (x1 : nadd) := ((exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))) -> exists y0 : nat, forall y1 : nat, (Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term43 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term23 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x1 y0))) x2.
Definition term86 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) (Nat.add x3 x4)).
Definition term63 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term69 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term60 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (dest_nadd x0 x1) (Nat.add x2 x3).
Definition term79 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.le x0 y0)) x1.
Definition term68 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1)) x1.
Definition term36 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (dist (@pair nat nat x0 y0)) y1) = ((Peano.le x0 (Nat.add y0 y1)) /\ (Peano.le y0 (Nat.add x0 y1)))) x1.
Definition term89 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term64 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term55 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dest_nadd x0 x1) x2) x3.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (dist (@pair nat nat x1 x0)) y0) = ((Peano.le x1 (Nat.add x0 y0)) /\ (Peano.le x0 (Nat.add x1 y0))).
Definition term20 (x0 : nadd) (x1 : nadd) := @eq Prop ((exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))).
Definition term37 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term13 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1))) x1.
Definition term9 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1)) x1.
Definition term42 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term52 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add (dest_nadd x0 y0) x1) y1) -> Peano.le (dest_nadd x2 y0) y1) x3.
Definition term78 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.le x0 y0).
Definition term67 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term51 (x0 : nadd) (x1 : nat) (x2 : nadd) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dest_nadd x0 y0) x1) y1) -> Peano.le (dest_nadd x2 y0) y1.
Definition term44 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term35 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> (Peano.le y0 y1) -> Peano.le x0 y1.
Definition term33 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> (Peano.le y1 y2) -> Peano.le y0 y2.
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (dist (@pair nat nat x0 y0)) y1) = ((Peano.le x0 (Nat.add y0 y1)) /\ (Peano.le y0 (Nat.add x0 y1))).
Definition term94 := forall y0 : nat, True.
Definition term97 (x0 : nadd) (x1 : nadd) := (exists y0 : nat, forall y1 : nat, (Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0))) -> (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 x0) -> (Peano.le x0 y0) -> Peano.le x1 y0) x2.
Definition term25 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x1 y0))) x2.
Definition term93 := fun y0 : nat => True.
Definition term56 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dest_nadd x0 x1) x2.
Definition term15 (x0 : nadd) (x1 : nadd) := and (nadd_le x0 x1).
Definition term53 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0) x4.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term83 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dest_nadd x0 x1) x3) (Nat.add (dest_nadd x0 x1) (Nat.add x2 x3)).
Definition term27 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term57 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dest_nadd x0 y0) x1) y1) -> Peano.le (dest_nadd x2 y0) y1) -> Peano.le (dest_nadd x2 x3) x4.
Definition term19 (x0 : nadd) (x1 : nadd) := @eq Prop ((nadd_le x1 x0) /\ (nadd_le x0 x1)).
Definition term73 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (dest_nadd x0 x1) x2) x3.
Definition term65 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term74 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (dest_nadd x0 x1) x2).
Definition term62 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> forall y2 : nat, (Peano.le y1 y2) -> Peano.le y0 y2) x0.
Definition term50 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := forall y0 : nat, (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0.
Definition term99 (x0 : nadd) := forall y0 : nadd, ((nadd_le x0 y0) /\ (nadd_le y0 x0)) = (nadd_eq x0 y0).
Definition term18 (x0 : nadd) (x1 : nadd) := (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term48 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.le (dest_nadd x2 x3) (Nat.add (dest_nadd x0 x3) x1)) -> forall y0 : nat, (Peano.le (Nat.add (dest_nadd x0 x3) x1) y0) -> Peano.le (dest_nadd x2 x3) y0.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0)) x2.
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) -> (Peano.le x0 x2) -> Peano.le x1 x2.
Definition term32 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) x3).
Definition term21 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2))) x3.
Definition term96 (x0 : Prop) := forall y0 : nat, x0.
Definition term12 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)).
Definition term8 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term41 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le x1 y0.
Definition term84 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dest_nadd x0 x1) x3) (Nat.add (Nat.add (dest_nadd x0 x1) x2) x3).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 (Nat.add x0 x2)) /\ (Peano.le x0 (Nat.add x1 x2)).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.le x0 x1)) x2.
Definition term54 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nat) (x4 : nat) := (Peano.le (Nat.add (dest_nadd x0 x3) x1) x4) -> Peano.le (dest_nadd x2 x3) x4.
Definition term47 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> forall y1 : nat, (Peano.le y0 y1) -> Peano.le x0 y1) x1.
Definition term28 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, (Peano.le (dest_nadd x1 y1) (Nat.add (dest_nadd x0 y1) y0)) /\ (Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0)).
Definition term87 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le (dest_nadd x1 x2) (Nat.add (dest_nadd x0 x2) (Nat.add x3 x4))) /\ (Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd x1 x2) (Nat.add x3 x4))).
Definition term88 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := forall y0 : nat, (Peano.le (dest_nadd x1 y0) (Nat.add (dest_nadd x0 y0) (Nat.add x2 x3))) /\ (Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x1 y0) (Nat.add x2 x3))).
Definition term75 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dest_nadd x0 x1) x2) (Nat.add (dest_nadd x0 x1) (Nat.add x2 x3)).
Definition term17 (x0 : nadd) (x1 : nadd) := (nadd_le x1 x0) /\ (nadd_le x0 x1).
