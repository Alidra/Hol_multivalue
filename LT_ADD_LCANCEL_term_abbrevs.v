Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Nat.add x1 x0) = (Nat.add (Nat.add x1 x2) (S y0)).
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term30 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 x1).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add x1 x0) (Nat.add x1 x2).
Definition term40 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term38 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.lt x1 y0).
Definition term17 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term23 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1))).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term2 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term42 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.lt y0 y1).
Definition term6 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term35 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, x0 = (Nat.add x1 (S y0))).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 (S x2)).
Definition term45 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.lt y1 y2).
Definition term43 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.lt y0 y1).
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term13 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term12 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term39 := forall y0 : nat, True.
Definition term37 := fun y0 : nat => True.
Definition term25 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 (S y0)).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.lt (Nat.add x1 x0) (Nat.add x1 x2)).
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 (S y2)))) x0.
Definition term33 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 (S y0)).
Definition term31 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term41 (x0 : Prop) := forall y0 : nat, x0.
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Nat.add x1 x0) = (Nat.add (Nat.add x1 x2) (S y0)).
Definition term3 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term36 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.lt x1 y0).
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1)))) x1.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) (S x2).
Definition term7 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term44 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.lt y1 y2).
Definition term11 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term10 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).