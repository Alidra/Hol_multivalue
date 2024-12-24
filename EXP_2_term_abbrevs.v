Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term41 (x0 : nat) := NUMERAL (BIT0 x0).
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term58 (x0 : nat) := Nat.mul x0 (Nat.pow x0 (NUMERAL 0)).
Definition term50 := Nat.add (S (NUMERAL 0)) (S (NUMERAL 0)).
Definition term15 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term57 (x0 : nat) := Nat.pow x0 (S (NUMERAL 0)).
Definition term67 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term47 := S (NUMERAL 0).
Definition term29 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term20 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term17 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term1 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term39 (x0 : nat) := S (Nat.add (NUMERAL x0) (NUMERAL x0)).
Definition term65 := forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0).
Definition term53 := S (S (NUMERAL 0)).
Definition term9 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term31 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term62 (x0 : nat) := @eq nat (Nat.mul x0 x0).
Definition term35 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term4 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term10 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term44 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term22 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term55 (x0 : nat) := Nat.pow x0 (S (S (NUMERAL 0))).
Definition term8 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term59 (x0 : nat) := Nat.mul x0 (S (NUMERAL 0)).
Definition term46 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term25 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term34 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term51 := S (Nat.add (NUMERAL 0) (S (NUMERAL 0))).
Definition term13 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term7 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term63 := fun y0 : nat => (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0).
Definition term27 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term18 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term2 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term66 := forall y0 : nat, True.
Definition term45 := S (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term52 := Nat.add (NUMERAL 0) (S (NUMERAL 0)).
Definition term11 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term32 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term12 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term37 (x0 : nat) := (fun y0 : nat => (NUMERAL (BIT1 y0)) = (S (Nat.add (NUMERAL y0) (NUMERAL y0)))) x0.
Definition term64 := fun y0 : nat => True.
Definition term54 (x0 : nat) := Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term40 (x0 : nat) := (fun y0 : nat => (NUMERAL (BIT0 y0)) = (Nat.add (NUMERAL y0) (NUMERAL y0))) x0.
Definition term48 := Nat.add (NUMERAL (BIT1 0)).
Definition term16 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term0 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term43 := NUMERAL (BIT0 (BIT1 0)).
Definition term61 (x0 : nat) := @eq nat (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term60 (x0 : nat) := Nat.add x0 (Nat.mul x0 (NUMERAL 0)).
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term33 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term24 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term23 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term26 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term49 := Nat.add (S (NUMERAL 0)).
Definition term42 (x0 : nat) := Nat.add (NUMERAL x0) (NUMERAL x0).
Definition term68 (x0 : Prop) := forall y0 : nat, x0.
Definition term14 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term56 (x0 : nat) := Nat.mul x0 (Nat.pow x0 (S (NUMERAL 0))).
Definition term38 (x0 : nat) := NUMERAL (BIT1 x0).
Definition term6 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term36 := NUMERAL (BIT1 0).
