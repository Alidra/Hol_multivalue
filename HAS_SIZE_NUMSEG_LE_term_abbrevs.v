Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat) := @HAS_SIZE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1)) x0.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.le x1 x2).
Definition term9 (x0 : nat) := (fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) x0.
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) = (Peano.lt x0 (S y0)).
Definition term36 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term23 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 (Peano.lt y0 (Nat.add x1 (NUMERAL (BIT1 0)))) y0.
Definition term25 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (Nat.add x0 (NUMERAL (BIT1 0)))) y1.
Definition term24 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1.
Definition term3 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = (Peano.le x0 y0).
Definition term32 := fun y0 : nat => @HAS_SIZE nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 y0) y2)) (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (Peano.lt x0 (S y0)).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.lt x1 (Nat.add x2 (NUMERAL (BIT1 0)))).
Definition term29 (x0 : nat) := @HAS_SIZE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (Nat.add x0 (NUMERAL (BIT1 0)))) y1)).
Definition term28 (x0 : nat) := @HAS_SIZE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1)).
Definition term5 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = (Peano.le y0 y1).
Definition term21 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 (Peano.lt y0 (Nat.add x1 (NUMERAL (BIT1 0)))) y0.
Definition term15 (x0 : nat) (x1 : nat) := Peano.lt x0 (Nat.add x1 (NUMERAL (BIT1 0))).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (Peano.lt y0 (S y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = (Peano.le y0 y1).
Definition term0 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term35 := forall y0 : nat, True.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.le x2 x1) x2.
Definition term10 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (Peano.lt x0 (S y0))) x1.
Definition term33 := fun y0 : nat => True.
Definition term22 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 (Peano.le y0 x1) y0.
Definition term1 (x0 : nat) := fun y0 : nat => (Peano.lt x0 (S y0)) = (Peano.le x0 y0).
Definition term11 (x0 : nat) := (fun y0 : nat => @HAS_SIZE nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2)) y0) x0.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.lt x2 (Nat.add x1 (NUMERAL (BIT1 0)))) x2.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (Peano.lt y0 (S y1))) x0.
Definition term20 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 (Peano.le y0 x1) y0.
Definition term34 := forall y0 : nat, @HAS_SIZE nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 y0) y2)) (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term37 (x0 : Prop) := forall y0 : nat, x0.
Definition term31 (x0 : nat) := @HAS_SIZE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (Nat.add x0 (NUMERAL (BIT1 0)))) y1)) (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term30 (x0 : nat) := @HAS_SIZE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1)) (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (Peano.lt y0 (S y1)).
Definition term27 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (Nat.add x0 (NUMERAL (BIT1 0)))) y1).
Definition term26 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1).
