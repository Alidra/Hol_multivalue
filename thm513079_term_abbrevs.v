Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term62 (x0 : nat) := @eq nat (S (BIT1 x0)).
Definition term41 (x0 : nat) := @eq nat (S (NUMERAL x0)).
Definition term23 := (forall y0 : nat, (Nat.add 0 y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 0) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term22 := (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term55 (x0 : nat) := @eq nat (S (BIT0 x0)).
Definition term64 (x0 : nat) := BIT0 (S x0).
Definition term48 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term43 (x0 : nat) := NUMERAL (S x0).
Definition term12 (x0 : nat) := @eq nat (Nat.add x0 0).
Definition term19 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term68 := fun y0 : nat => (S (BIT1 y0)) = (BIT0 (S y0)).
Definition term56 (x0 : nat) := @eq nat (S (Nat.add x0 x0)).
Definition term71 := ((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)))).
Definition term44 := fun y0 : nat => (S (NUMERAL y0)) = (NUMERAL (S y0)).
Definition term40 (x0 : nat) := S (NUMERAL x0).
Definition term32 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term67 (x0 : nat) := Nat.add x0 (S x0).
Definition term13 := fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0.
Definition term10 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term63 (x0 : nat) := @eq nat (S (S (Nat.add x0 x0))).
Definition term37 (x0 : nat) := S (Nat.add x0 x0).
Definition term2 (x0 : nat) := @eq nat (Nat.add (NUMERAL 0) x0).
Definition term15 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term60 (x0 : nat) := S (BIT1 x0).
Definition term38 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term11 (x0 : nat) := @eq nat (Nat.add x0 (NUMERAL 0)).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term59 := and (forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)).
Definition term50 := and (forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0))).
Definition term65 (x0 : nat) := Nat.add (S x0) (S x0).
Definition term39 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term1 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term14 := fun y0 : nat => (Nat.add y0 0) = y0.
Definition term29 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term18 := and (forall y0 : nat, (Nat.add y0 0) = y0).
Definition term17 := and (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0).
Definition term9 := and (forall y0 : nat, (Nat.add 0 y0) = y0).
Definition term8 := and (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0).
Definition term30 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term24 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term47 := forall y0 : nat, True.
Definition term52 := @eq nat (S 0).
Definition term7 := forall y0 : nat, (Nat.add 0 y0) = y0.
Definition term6 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term35 (x0 : nat) := (fun y0 : nat => (Nat.add 0 y0) = y0) x0.
Definition term51 := S (Nat.add 0 0).
Definition term5 := fun y0 : nat => (Nat.add 0 y0) = y0.
Definition term45 := fun y0 : nat => True.
Definition term36 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term69 := forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)).
Definition term21 := (forall y0 : nat, (Nat.add y0 0) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term20 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term57 := fun y0 : nat => (S (BIT0 y0)) = (BIT1 y0).
Definition term53 := and ((S 0) = (BIT1 0)).
Definition term70 := (forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))).
Definition term42 (x0 : nat) := @eq nat (S x0).
Definition term0 := Nat.add (NUMERAL 0).
Definition term31 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term46 := forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0)).
Definition term16 := forall y0 : nat, (Nat.add y0 0) = y0.
Definition term28 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term49 (x0 : Prop) := forall y0 : nat, x0.
Definition term4 := fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0.
Definition term54 (x0 : nat) := S (BIT0 x0).
Definition term3 (x0 : nat) := @eq nat (Nat.add 0 x0).
Definition term72 := (forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0))) /\ (((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))))).
Definition term66 (x0 : nat) := S (Nat.add x0 (S x0)).
Definition term58 := forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0).
Definition term34 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term61 (x0 : nat) := S (S (Nat.add x0 x0)).
Definition term26 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
