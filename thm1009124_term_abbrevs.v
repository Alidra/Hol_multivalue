Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => ((Nat.mul x0 y0) = x2) -> (Nat.pow x0 (BIT1 x1)) = x2) x3).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.mul x0 x0) = x1) -> ((Nat.mul x2 x1) = x4) -> (Nat.pow x2 (BIT1 x3)) = x4.
Definition term30 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.mul (Nat.pow x0 x1) (Nat.pow x0 x1)).
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow y0 (Nat.add y1 y2)) = (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2))) x0.
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x0 (BIT1 x1)) = y0) x2.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x0 (Nat.mul (Nat.pow x0 x1) (Nat.pow x0 x1))) = x2) -> (Nat.pow x0 (BIT1 x1)) = x2.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Nat.mul y0 y0) = x0) -> ((Nat.mul x2 x0) = x1) -> (Nat.pow x2 (BIT1 x3)) = x1) (Nat.pow x2 x3).
Definition term2 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((Nat.mul x0 y0) = x2) -> (Nat.pow x0 (BIT1 x1)) = x2.
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => ((Nat.mul y0 y0) = x0) -> ((Nat.mul x1 x0) = x3) -> (Nat.pow x1 (BIT1 x2)) = x3.
Definition term4 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((Nat.mul y0 y0) = x0) -> ((Nat.mul x1 x0) = x3) -> (Nat.pow x1 (BIT1 x2)) = x3) x4.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (BIT1 x1)) = y0) (Nat.mul x0 (Nat.mul (Nat.pow x0 x1) (Nat.pow x0 x1))).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1))) x1.
Definition term14 (x0 : nat) := S (Nat.add x0 x0).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 x2).
Definition term38 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 (Nat.add x1 x1)).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul (Nat.pow x1 x2) (Nat.pow x1 x2)) = x0) -> ((Nat.mul x1 x0) = x3) -> (Nat.pow x1 (BIT1 x2)) = x3.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul x1 x0) = x3) -> (Nat.pow x1 (BIT1 x2)) = x3.
Definition term7 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)).
Definition term0 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term34 (x0 : nat) (x1 : nat) := Nat.pow x0 (BIT1 x1).
Definition term31 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.pow x0 (BIT1 x1)) = y0.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop ((fun y0 : nat => ((Nat.mul y0 y0) = x0) -> ((Nat.mul x1 x0) = x3) -> (Nat.pow x1 (BIT1 x2)) = x3) x4).
Definition term5 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.mul x1 x0) = x3) -> (Nat.pow x1 (BIT1 x2)) = x3).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.pow x2 x3) = x0) -> ((Nat.mul x0 x0) = x1) -> ((Nat.mul x2 x1) = x4) -> (Nat.pow x2 (BIT1 x3)) = x4.
Definition term9 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0)).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.mul x1 y0) = x0) -> (Nat.pow x1 (BIT1 x2)) = x0) (Nat.mul (Nat.pow x1 x2) (Nat.pow x1 x2)).
Definition term13 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term39 (x0 : nat) (x1 : nat) := Nat.pow x0 (Nat.add x1 x1).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => (Nat.pow x0 (BIT1 x1)) = y0) x2).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.pow x0 (BIT1 x1)) = x2).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) x2.
Definition term37 (x0 : nat) (x1 : nat) := Nat.pow x0 (S (Nat.add x1 x1)).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop (((Nat.mul x0 x0) = x1) -> ((Nat.mul x2 x1) = x4) -> (Nat.pow x2 (BIT1 x3)) = x4).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term41 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 (Nat.mul (Nat.pow x0 x1) (Nat.pow x0 x1))).
Definition term40 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 (BIT1 x1)).
Definition term22 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow x0 x1) (Nat.pow x0 x1).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = x2) -> (Nat.pow x0 (BIT1 x1)) = x2) x3.
