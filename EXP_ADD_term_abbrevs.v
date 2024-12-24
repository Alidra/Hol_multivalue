Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : nat) (x1 : nat) := Nat.pow x0 (Nat.add x1 (NUMERAL 0)).
Definition term26 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) y0.
Definition term31 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term58 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term49 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.pow x1 (Nat.add x0 x2)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2))).
Definition term27 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) y0.
Definition term22 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) y0) -> (fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) (S y0)).
Definition term38 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term34 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term60 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term1 (x0 : nat) (x1 : nat) := (((fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) y0) -> (fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) y0.
Definition term59 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term42 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term24 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) y0) -> (fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) (S y0))).
Definition term39 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term5 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (NUMERAL 0)).
Definition term20 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) y0) -> (fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) (S y0).
Definition term37 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term33 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term47 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow x0 x1) (NUMERAL (BIT1 0)).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 x2).
Definition term6 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) (NUMERAL 0)).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.pow x1 (Nat.add x0 x2)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2))) -> (Nat.pow x1 (Nat.add x0 (S x2))) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (S x2))).
Definition term41 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term18 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) y0) -> (fun y1 : nat => (Nat.pow x1 (Nat.add x0 y1)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y1))) (S y0).
Definition term55 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (S x2)).
Definition term70 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.pow y0 (Nat.add y1 y2)) = (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2)).
Definition term69 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)).
Definition term56 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term50 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.add x1 (S x2)).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.mul x1 (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2))).
Definition term7 (x0 : nat) (x1 : nat) := and ((Nat.pow x1 (Nat.add x0 (NUMERAL 0))) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (NUMERAL 0)))).
Definition term29 (x0 : nat) (x1 : nat) := (((Nat.pow x1 (Nat.add x0 (NUMERAL 0))) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (NUMERAL 0)))) /\ (forall y0 : nat, ((Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) -> (Nat.pow x1 (Nat.add x0 (S y0))) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (S y0))))) -> forall y0 : nat, (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0)).
Definition term61 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term28 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0)).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.pow x0 (Nat.add x1 x2)).
Definition term53 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term45 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 x1).
Definition term36 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term32 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.pow x0 (Nat.add x1 (S x2))).
Definition term35 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.mul x1 (Nat.pow x1 x2)).
Definition term57 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term51 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term40 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) x2.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) (S x2).
Definition term54 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.mul x1 x0) x2) = (Nat.mul x1 (Nat.mul x0 x2))) /\ ((Nat.mul x1 (Nat.mul x0 x2)) = (Nat.mul x0 (Nat.mul x1 x2))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term25 (x0 : nat) (x1 : nat) := imp (((Nat.pow x1 (Nat.add x0 (NUMERAL 0))) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (NUMERAL 0)))) /\ (forall y0 : nat, ((Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) -> (Nat.pow x1 (Nat.add x0 (S y0))) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (S y0))))).
Definition term23 (x0 : nat) (x1 : nat) := ((Nat.pow x1 (Nat.add x0 (NUMERAL 0))) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (NUMERAL 0)))) /\ (forall y0 : nat, ((Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) -> (Nat.pow x1 (Nat.add x0 (S y0))) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (S y0)))).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x1 (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term21 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) -> (Nat.pow x1 (Nat.add x0 (S y0))) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (S y0))).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (S (Nat.add x1 x2)).
Definition term19 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) -> (Nat.pow x1 (Nat.add x0 (S y0))) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 (S y0))).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) x2) -> (fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) (S x2).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) x2).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) (NUMERAL 0).
Definition term30 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term43 := NUMERAL (BIT1 0).
Definition term44 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 (Nat.add x1 (NUMERAL 0))).
Definition term46 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow x0 x1).
Definition term2 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0)).
Definition term52 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
