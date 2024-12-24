Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x1) (Nat.add x0 x1).
Definition term16 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x0 (Nat.add x1 x1)).
Definition term34 := (forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))))))))).
Definition term33 := (forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)))))))).
Definition term32 := (forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))))))).
Definition term15 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x0) (Nat.add x1 x1).
Definition term4 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term28 := (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term35 := (0 = 0) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)))))))))).
Definition term17 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.add x0 x0) (Nat.add x1 x1)).
Definition term23 (x0 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x0) (Nat.add y0 y0)) = (Nat.add (Nat.add x0 y0) (Nat.add x0 y0)).
Definition term6 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1).
Definition term30 := (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))))).
Definition term0 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add x0 y0).
Definition term29 := (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)))).
Definition term12 := and (forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)).
Definition term11 := forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0).
Definition term2 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add x0 y0).
Definition term20 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x0 x1)).
Definition term26 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1).
Definition term3 := forall y0 : nat, True.
Definition term1 := fun y0 : nat => True.
Definition term24 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x0) (Nat.add y0 y0)) = (Nat.add (Nat.add x0 y0) (Nat.add x0 y0)).
Definition term9 := and (0 = 0).
Definition term10 := fun y0 : nat => (Nat.add y0 y0) = (Nat.add y0 y0).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term21 (x0 : nat) (x1 : nat) := Nat.add x1 (Nat.add x0 x1).
Definition term27 := and (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))).
Definition term8 := and (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)).
Definition term5 (x0 : Prop) := forall y0 : nat, x0.
Definition term36 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)) /\ ((0 = 0) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))))))))))).
Definition term18 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 (Nat.add x0 (Nat.add x1 x1))).
Definition term31 := (forall y0 : nat, (Nat.add y0 y0) = (Nat.add y0 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)))))).
Definition term22 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x1 x1).
Definition term25 := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.add y0 y1) (Nat.add y0 y1)).
