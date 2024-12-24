Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 (Nat.mul (Nat.pow x0 x2) (Nat.pow x1 x2))).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow (Nat.mul x0 x1) (S x2).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x0 x2) (Nat.mul x1 (Nat.pow x1 x2)).
Definition term28 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) x0.
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term14 (x0 : nat) := (forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) x0) = (Nat.mul (Nat.pow y0 x0) (Nat.pow y1 x0))) -> forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) (S x0)) = (Nat.mul (Nat.pow y0 (S x0)) (Nat.pow y1 (S x0))).
Definition term47 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.mul x0 (Nat.mul x1 (Nat.mul (Nat.pow x0 x2) (Nat.pow x1 x2)))).
Definition term18 := forall y0 : nat, (forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) -> forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) (S y0)) = (Nat.mul (Nat.pow y1 (S y0)) (Nat.pow y2 (S y0))).
Definition term53 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term26 := ((forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) (NUMERAL 0)) = (Nat.mul (Nat.pow y0 (NUMERAL 0)) (Nat.pow y1 (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) -> forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) (S y0)) = (Nat.mul (Nat.pow y1 (S y0)) (Nat.pow y2 (S y0))))) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0)).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow (Nat.mul x0 x1) x2.
Definition term36 (x0 : nat) (x1 : nat) := Nat.pow (Nat.mul x0 x1) (NUMERAL 0).
Definition term9 (x0 : nat) := imp ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) x0).
Definition term55 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term1 := (((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) y0.
Definition term54 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term73 (x0 : nat) (x1 : nat) := Nat.mul (Nat.mul x0 (Nat.pow x0 x1)).
Definition term34 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow (Nat.mul x0 y0) x1) = (Nat.mul (Nat.pow x0 x1) (Nat.pow y0 x1))) x2.
Definition term21 := imp (((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) (S y0))).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 (Nat.pow (Nat.mul x0 x1) x2)).
Definition term79 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow (Nat.mul x0 y0) (S x1)) = (Nat.mul (Nat.pow x0 (S x1)) (Nat.pow y0 (S x1))).
Definition term45 (x0 : nat) := forall y0 : nat, (Nat.pow (Nat.mul x0 y0) (NUMERAL 0)) = (Nat.mul (Nat.pow x0 (NUMERAL 0)) (Nat.pow y0 (NUMERAL 0))).
Definition term57 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow (Nat.mul y0 y1) x0) = (Nat.mul (Nat.pow y0 x0) (Nat.pow y1 x0))) x1.
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.pow x0 (S x2)) (Nat.pow x1 (S x2)).
Definition term17 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) (S y0).
Definition term42 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term39 (x0 : nat) := Nat.mul (Nat.pow x0 (NUMERAL 0)).
Definition term5 := and ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) (NUMERAL 0)).
Definition term72 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow x0 (S x1)).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) (S x0).
Definition term3 := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) (NUMERAL 0).
Definition term33 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term22 := imp ((forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) (NUMERAL 0)) = (Nat.mul (Nat.pow y0 (NUMERAL 0)) (Nat.pow y1 (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) -> forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) (S y0)) = (Nat.mul (Nat.pow y1 (S y0)) (Nat.pow y2 (S y0))))).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term51 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term25 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0)).
Definition term12 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) (S x0)) = (Nat.mul (Nat.pow y0 (S x0)) (Nat.pow y1 (S x0))).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) x0) = (Nat.mul (Nat.pow y0 x0) (Nat.pow y1 x0)).
Definition term4 := forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) (NUMERAL 0)) = (Nat.mul (Nat.pow y0 (NUMERAL 0)) (Nat.pow y1 (NUMERAL 0))).
Definition term46 := forall y0 : nat, True.
Definition term29 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term56 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term30 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term41 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow x0 (NUMERAL 0)) (Nat.pow x1 (NUMERAL 0)).
Definition term44 := fun y0 : nat => True.
Definition term43 (x0 : nat) := fun y0 : nat => (Nat.pow (Nat.mul x0 y0) (NUMERAL 0)) = (Nat.mul (Nat.pow x0 (NUMERAL 0)) (Nat.pow y0 (NUMERAL 0))).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 (Nat.pow x0 x2)) (Nat.mul x1 (Nat.pow x1 x2)).
Definition term15 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) (S y0).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x1 (Nat.mul (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term37 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (Nat.mul x0 x1) (NUMERAL 0)).
Definition term6 := and (forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) (NUMERAL 0)) = (Nat.mul (Nat.pow y0 (NUMERAL 0)) (Nat.pow y1 (NUMERAL 0)))).
Definition term23 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) y0.
Definition term38 := @eq nat (NUMERAL (BIT1 0)).
Definition term52 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term16 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) -> forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) (S y0)) = (Nat.mul (Nat.pow y1 (S y0)) (Nat.pow y2 (S y0))).
Definition term32 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x1 (Nat.pow (Nat.mul x0 x1) x2).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term19 := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) y0) -> (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) (S y0)).
Definition term58 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow (Nat.mul x0 y0) x1) = (Nat.mul (Nat.pow x0 x1) (Nat.pow y0 x1)).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.mul x1 x0) x2) = (Nat.mul x1 (Nat.mul x0 x2))) /\ ((Nat.mul x1 (Nat.mul x0 x2)) = (Nat.mul x0 (Nat.mul x1 x2))).
Definition term48 (x0 : Prop) := forall y0 : nat, x0.
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) (Nat.pow (Nat.mul x0 x1) x2).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul (Nat.pow x0 x2) (Nat.mul x1 (Nat.pow x1 x2))).
Definition term78 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.pow (Nat.mul x0 y0) (S x1)) = (Nat.mul (Nat.pow x0 (S x1)) (Nat.pow y0 (S x1))).
Definition term40 := Nat.mul (NUMERAL (BIT1 0)).
Definition term13 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) x0) -> (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) (S x0).
Definition term24 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.pow (Nat.mul y2 y3) y1) = (Nat.mul (Nat.pow y2 y1) (Nat.pow y3 y1))) y0.
Definition term10 (x0 : nat) := imp (forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) x0) = (Nat.mul (Nat.pow y0 x0) (Nat.pow y1 x0))).
Definition term27 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term20 := (forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.mul y0 y1) (NUMERAL 0)) = (Nat.mul (Nat.pow y0 (NUMERAL 0)) (Nat.pow y1 (NUMERAL 0)))) /\ (forall y0 : nat, (forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0))) -> forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) (S y0)) = (Nat.mul (Nat.pow y1 (S y0)) (Nat.pow y2 (S y0)))).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.pow (Nat.mul x0 x1) (S x2)).
Definition term80 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.pow (Nat.mul y0 y1) (S x0)) = (Nat.mul (Nat.pow y0 (S x0)) (Nat.pow y1 (S x0))).
Definition term49 := fun y0 : nat => forall y1 : nat, (Nat.pow (Nat.mul y0 y1) (NUMERAL 0)) = (Nat.mul (Nat.pow y0 (NUMERAL 0)) (Nat.pow y1 (NUMERAL 0))).
Definition term35 := NUMERAL (BIT1 0).
Definition term31 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term2 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.mul y1 y2) y0) = (Nat.mul (Nat.pow y1 y0) (Nat.pow y2 y0)).
