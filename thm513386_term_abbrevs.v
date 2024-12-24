Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term40 (x0 : nat) := Nat.pred (BIT1 x0).
Definition term17 (x0 : nat) := NUMERAL (Nat.pred x0).
Definition term50 := (forall y0 : nat, (Nat.pred (NUMERAL y0)) = (NUMERAL (Nat.pred y0))) /\ (((Nat.pred 0) = 0) /\ ((forall y0 : nat, (Nat.pred (BIT0 y0)) = (@COND nat (y0 = 0) 0 (BIT1 (Nat.pred y0)))) /\ (forall y0 : nat, (Nat.pred (BIT1 y0)) = (BIT0 y0)))).
Definition term25 (x0 : nat) := Nat.pred (BIT0 x0).
Definition term22 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term45 := forall y0 : nat, (Nat.pred (BIT1 y0)) = (BIT0 y0).
Definition term3 := and ((Nat.pred (NUMERAL 0)) = (NUMERAL 0)).
Definition term29 (x0 : nat) := BIT1 (Nat.pred x0).
Definition term32 (x0 : nat) := @COND nat (x0 = 0) 0 (BIT1 (Nat.pred x0)).
Definition term34 := fun y0 : nat => (Nat.pred (BIT0 y0)) = (@COND nat (y0 = 0) 0 (BIT1 (Nat.pred y0))).
Definition term48 := ((Nat.pred 0) = 0) /\ ((forall y0 : nat, (Nat.pred (BIT0 y0)) = (@COND nat (y0 = 0) 0 (BIT1 (Nat.pred y0)))) /\ (forall y0 : nat, (Nat.pred (BIT1 y0)) = (BIT0 y0))).
Definition term14 (x0 : nat) := Nat.pred (NUMERAL x0).
Definition term12 (x0 : nat) := S (Nat.add x0 x0).
Definition term47 := (forall y0 : nat, (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))) /\ True.
Definition term10 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term43 (x0 : nat) := @eq nat (Nat.add x0 x0).
Definition term39 := and (forall y0 : nat, (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))).
Definition term38 := and (forall y0 : nat, (Nat.pred (BIT0 y0)) = (@COND nat (y0 = 0) 0 (BIT1 (Nat.pred y0)))).
Definition term24 := and (forall y0 : nat, (Nat.pred (NUMERAL y0)) = (NUMERAL (Nat.pred y0))).
Definition term13 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term49 := True /\ (forall y0 : nat, (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0))))).
Definition term35 := fun y0 : nat => (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0)))).
Definition term21 := forall y0 : nat, True.
Definition term37 := forall y0 : nat, (Nat.pred (Nat.add y0 y0)) = (@COND nat (y0 = 0) 0 (S (Nat.add (Nat.pred y0) (Nat.pred y0)))).
Definition term36 := forall y0 : nat, (Nat.pred (BIT0 y0)) = (@COND nat (y0 = 0) 0 (BIT1 (Nat.pred y0))).
Definition term44 := fun y0 : nat => (Nat.pred (BIT1 y0)) = (BIT0 y0).
Definition term19 := fun y0 : nat => True.
Definition term30 (x0 : nat) := S (Nat.add (Nat.pred x0) (Nat.pred x0)).
Definition term11 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term26 (x0 : nat) := Nat.pred (Nat.add x0 x0).
Definition term5 := forall y0 : nat, (Nat.pred (S y0)) = y0.
Definition term46 := (forall y0 : nat, (Nat.pred (BIT0 y0)) = (@COND nat (y0 = 0) 0 (BIT1 (Nat.pred y0)))) /\ (forall y0 : nat, (Nat.pred (BIT1 y0)) = (BIT0 y0)).
Definition term4 := and ((Nat.pred 0) = 0).
Definition term6 := ((Nat.pred (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, (Nat.pred (S y0)) = y0).
Definition term15 (x0 : nat) := @eq nat (Nat.pred (NUMERAL x0)).
Definition term42 (x0 : nat) := @eq nat (Nat.pred (BIT1 x0)).
Definition term20 := forall y0 : nat, (Nat.pred (NUMERAL y0)) = (NUMERAL (Nat.pred y0)).
Definition term2 := @eq nat (Nat.pred 0).
Definition term0 := Nat.pred (NUMERAL 0).
Definition term33 (x0 : nat) := @COND nat (x0 = 0) 0 (S (Nat.add (Nat.pred x0) (Nat.pred x0))).
Definition term28 (x0 : nat) := @eq nat (Nat.pred (Nat.add x0 x0)).
Definition term41 (x0 : nat) := Nat.pred (S (Nat.add x0 x0)).
Definition term7 := ((Nat.pred 0) = 0) /\ (forall y0 : nat, (Nat.pred (S y0)) = y0).
Definition term23 (x0 : Prop) := forall y0 : nat, x0.
Definition term31 (x0 : nat) := @COND nat (x0 = 0) 0.
Definition term16 (x0 : nat) := @eq nat (Nat.pred x0).
Definition term27 (x0 : nat) := @eq nat (Nat.pred (BIT0 x0)).
Definition term8 (x0 : nat) := (fun y0 : nat => (Nat.pred (S y0)) = y0) x0.
Definition term1 := @eq nat (Nat.pred (NUMERAL 0)).
Definition term18 := fun y0 : nat => (Nat.pred (NUMERAL y0)) = (NUMERAL (Nat.pred y0)).
Definition term9 (x0 : nat) := Nat.pred (S x0).
