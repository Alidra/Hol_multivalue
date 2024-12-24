Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2))) x0.
Definition term34 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term32 (x0 : nadd) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (Nat.mul x1 y1) y0).
Definition term10 (x0 : nadd) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd (nadd_of_num x1) y1) y0).
Definition term8 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term40 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term27 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (Nat.mul x1 y0) x2).
Definition term26 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd (nadd_of_num x1) y0) x2).
Definition term20 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term41 (x0 : Prop) := forall y0 : nadd, x0.
Definition term29 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (Nat.mul x1 y0) x2).
Definition term28 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd (nadd_of_num x1) y0) x2).
Definition term39 := forall y0 : nadd, True.
Definition term35 (x0 : nadd) := exists y0 : nat, nadd_le x0 (nadd_of_num y0).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => Nat.mul x0 y0) x1.
Definition term31 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (Nat.mul x1 y1) y0).
Definition term30 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd (nadd_of_num x1) y1) y0).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd (nadd_of_num x0) x1) x2.
Definition term3 (x0 : nat) := dest_nadd (nadd_of_num x0).
Definition term16 (x0 : nat) := fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0.
Definition term7 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1))) x1.
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term14 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term23 (x0 : nadd) (x1 : nat) := Peano.le (dest_nadd x0 x1).
Definition term11 (x0 : nat) (x1 : nat) := dest_nadd (nadd_of_num x0) x1.
Definition term38 := forall y0 : nadd, exists y1 : nat, nadd_le y0 (nadd_of_num y1).
Definition term4 (x0 : nat) := fun y0 : nat => Nat.mul x0 y0.
Definition term2 (x0 : nat) := (fun y0 : nat => (dest_nadd (nadd_of_num y0)) = (fun y1 : nat => Nat.mul y0 y1)) x0.
Definition term37 := fun y0 : nadd => True.
Definition term17 (x0 : nat) (x1 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) x1).
Definition term25 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (Nat.mul x1 x2) x3).
Definition term24 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (dest_nadd (nadd_of_num x1) x2) x3).
Definition term0 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (Nat.mul y1 y3) y2)) x0.
Definition term6 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)).
Definition term1 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term18 (x0 : nat) (x1 : nat) := @eq nat ((fun y0 : nat => Nat.mul x0 y0) x1).
Definition term36 := fun y0 : nadd => exists y1 : nat, nadd_le y0 (nadd_of_num y1).
Definition term9 (x0 : nadd) (x1 : nat) := nadd_le x0 (nadd_of_num x1).
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) x1.
Definition term33 (x0 : nadd) := fun y0 : nat => nadd_le x0 (nadd_of_num y0).
Definition term19 (x0 : nat) (x1 : nat) := Nat.add (dest_nadd (nadd_of_num x0) x1).
