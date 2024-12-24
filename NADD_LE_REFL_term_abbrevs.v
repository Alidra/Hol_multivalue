Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2))) x0.
Definition term8 (x0 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x0 y1) y0).
Definition term7 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term9 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dest_nadd x0 x1) (Nat.add (dest_nadd x0 x1) x2).
Definition term20 := fun y0 : nadd => nadd_le y0 y0.
Definition term14 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term24 (x0 : Prop) := forall y0 : nadd, x0.
Definition term23 := forall y0 : nadd, True.
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term17 := exists y0 : nat, True.
Definition term16 (x0 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x0 y1) y0).
Definition term22 := forall y0 : nadd, nadd_le y0 y0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term6 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1))) x1.
Definition term19 (x0 : Prop) := exists y0 : nat, x0.
Definition term13 := forall y0 : nat, True.
Definition term11 := fun y0 : nat => True.
Definition term18 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term21 := fun y0 : nadd => True.
Definition term15 (x0 : Prop) := forall y0 : nat, x0.
Definition term5 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)).
Definition term12 (x0 : nadd) (x1 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x0 y0) x1).
Definition term10 (x0 : nadd) (x1 : nat) := fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (dest_nadd x0 y0) x1).
