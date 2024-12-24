Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term61 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul x0 x1) x1).
Definition term27 := @eq nat (NUMERAL 0).
Definition term72 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term20 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term45 (x0 : nat) := Nat.mul (S (NUMERAL 0)) x0.
Definition term74 := (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))))).
Definition term31 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term41 := S (NUMERAL 0).
Definition term8 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term70 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term25 (x0 : nat) := S (Nat.add (NUMERAL x0) (NUMERAL x0)).
Definition term50 := fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term21 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term2 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term65 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 (S x1)).
Definition term56 (x0 : nat) := @eq nat (Nat.mul x0 (NUMERAL (BIT1 0))).
Definition term3 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term57 := fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term18 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term63 := fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term10 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term43 := Nat.mul (S (NUMERAL 0)).
Definition term58 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term1 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term54 (x0 : nat) := Nat.mul x0 (S (NUMERAL 0)).
Definition term40 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term34 (x0 : nat) := @eq nat (Nat.mul x0 (NUMERAL 0)).
Definition term12 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term49 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term37 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term33 := and (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)).
Definition term47 (x0 : nat) := Nat.add (Nat.mul (NUMERAL 0) x0).
Definition term6 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term59 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0).
Definition term52 := and (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0).
Definition term26 (x0 : nat) := @eq nat (Nat.mul (NUMERAL 0) x0).
Definition term69 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term14 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term46 (x0 : nat) := Nat.add (Nat.mul (NUMERAL 0) x0) x0.
Definition term60 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (S x0) x1).
Definition term30 := forall y0 : nat, True.
Definition term39 := S (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term51 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term4 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term5 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term16 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term23 (x0 : nat) := (fun y0 : nat => (NUMERAL (BIT1 y0)) = (S (Nat.add (NUMERAL y0) (NUMERAL y0)))) x0.
Definition term29 := fun y0 : nat => True.
Definition term66 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 (Nat.mul x0 x1)).
Definition term35 := fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term71 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term0 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term62 (x0 : nat) := fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term48 := Nat.add (NUMERAL 0).
Definition term64 := and (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)).
Definition term53 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term55 (x0 : nat) := Nat.add x0 (Nat.mul x0 (NUMERAL 0)).
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term36 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term19 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term11 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term13 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term32 (x0 : Prop) := forall y0 : nat, x0.
Definition term22 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term67 (x0 : nat) := fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term42 := Nat.mul (NUMERAL (BIT1 0)).
Definition term73 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term24 (x0 : nat) := NUMERAL (BIT1 x0).
Definition term68 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term38 := NUMERAL (BIT1 0).
Definition term44 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term28 := fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
