Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => ((Nat.mul y0 y0) = x2) -> (Nat.pow x0 (BIT0 x1)) = x2) x3).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow y0 (Nat.add y1 y2)) = (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2))) x0.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x0 (BIT0 x1)) = y0) x2.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.pow x0 x1) (Nat.pow x0 x1)) = x2) -> (Nat.pow x0 (BIT0 x1)) = x2.
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((Nat.mul y0 y0) = x2) -> (Nat.pow x0 (BIT0 x1)) = x2.
Definition term19 (x0 : nat) (x1 : nat) := Nat.pow x0 (BIT0 x1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1))) x1.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 x2).
Definition term23 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 (BIT0 x1)).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.mul y0 y0) = x0) -> (Nat.pow x1 (BIT0 x2)) = x0) (Nat.pow x1 x2).
Definition term7 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul x0 x0) = x3) -> (Nat.pow x1 (BIT0 x2)) = x3.
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)).
Definition term16 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.pow x0 (BIT0 x1)) = y0.
Definition term24 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (Nat.pow x0 x1) (Nat.pow x0 x1)).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.mul x0 x0) = x3) -> (Nat.pow x1 (BIT0 x2)) = x3).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0)).
Definition term22 (x0 : nat) (x1 : nat) := Nat.pow x0 (Nat.add x1 x1).
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (BIT0 x1)) = y0) (Nat.mul (Nat.pow x0 x1) (Nat.pow x0 x1)).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => (Nat.pow x0 (BIT0 x1)) = y0) x2).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.pow x0 (BIT0 x1)) = x2).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) x2.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term15 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow x0 x1) (Nat.pow x0 x1).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Nat.mul y0 y0) = x2) -> (Nat.pow x0 (BIT0 x1)) = x2) x3.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.pow x1 x2) = x0) -> ((Nat.mul x0 x0) = x3) -> (Nat.pow x1 (BIT0 x2)) = x3.
