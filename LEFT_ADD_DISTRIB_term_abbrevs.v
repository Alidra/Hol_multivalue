Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term59 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term53 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) x0.
Definition term39 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)) (Nat.mul x0 x1).
Definition term44 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (x0 : nat) := forall y0 : nat, (forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) -> forall y1 : nat, (Nat.mul x0 (Nat.add (S y0) y1)) = (Nat.add (Nat.mul x0 (S y0)) (Nat.mul x0 y1)).
Definition term58 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term55 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term37 (x0 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) (S x1).
Definition term26 (x0 : nat) := ((forall y0 : nat, (Nat.mul x0 (Nat.add (NUMERAL 0) y0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (Nat.mul x0 y0))) /\ (forall y0 : nat, (forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) -> forall y1 : nat, (Nat.mul x0 (Nat.add (S y0) y1)) = (Nat.add (Nat.mul x0 (S y0)) (Nat.mul x0 y1)))) -> forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term1 (x0 : nat) := (((fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) y0.
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (S (Nat.add x1 x2)).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.mul x0 (Nat.add (S x1) x2)).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term64 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term21 (x0 : nat) := imp (((fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) (S y0))).
Definition term49 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term48 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1)) x1.
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term17 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) (S y0).
Definition term60 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term29 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term65 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term5 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) (NUMERAL 0)).
Definition term10 (x0 : nat) (x1 : nat) := imp (forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))).
Definition term6 (x0 : nat) := and (forall y0 : nat, (Nat.mul x0 (Nat.add (NUMERAL 0) y0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (Nat.mul x0 y0))).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) (NUMERAL 0).
Definition term33 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term22 (x0 : nat) := imp ((forall y0 : nat, (Nat.mul x0 (Nat.add (NUMERAL 0) y0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (Nat.mul x0 y0))) /\ (forall y0 : nat, (forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) -> forall y1 : nat, (Nat.mul x0 (Nat.add (S y0) y1)) = (Nat.add (Nat.mul x0 (S y0)) (Nat.mul x0 y1)))).
Definition term67 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term82 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2)).
Definition term62 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term56 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term47 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term25 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term43 := forall y0 : nat, True.
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.mul x0 (Nat.add x1 x2)).
Definition term31 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term32 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term42 := fun y0 : nat => True.
Definition term12 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add (S x0) y0)) = (Nat.add (Nat.mul x1 (S x0)) (Nat.mul x1 y0)).
Definition term8 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term4 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.add (NUMERAL 0) y0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (Nat.mul x0 y0)).
Definition term9 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1).
Definition term16 (x0 : nat) := fun y0 : nat => (forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) -> forall y1 : nat, (Nat.mul x0 (Nat.add (S y0) y1)) = (Nat.add (Nat.mul x0 (S y0)) (Nat.mul x0 y1)).
Definition term15 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) (S y0).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x1 (Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2)).
Definition term78 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)).
Definition term54 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term13 (x0 : nat) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1) -> (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) (S x1).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term20 (x0 : nat) := (forall y0 : nat, (Nat.mul x0 (Nat.add (NUMERAL 0) y0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (Nat.mul x0 y0))) /\ (forall y0 : nat, (forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) -> forall y1 : nat, (Nat.mul x0 (Nat.add (S y0) y1)) = (Nat.add (Nat.mul x0 (S y0)) (Nat.mul x0 y1))).
Definition term38 := Nat.add (NUMERAL 0).
Definition term40 (x0 : nat) (x1 : nat) := Nat.add (NUMERAL 0) (Nat.mul x0 x1).
Definition term23 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) y0.
Definition term63 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term57 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add (S x1) x2).
Definition term28 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term19 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) y0) -> (fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) (S y0)).
Definition term61 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0)) x2.
Definition term30 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term79 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.add x1 (Nat.mul x1 x0)) (Nat.mul x1 x2)).
Definition term35 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 (Nat.add (NUMERAL 0) x1)).
Definition term81 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x1 (Nat.add (S x0) y0)) = (Nat.add (Nat.mul x1 (S x0)) (Nat.mul x1 y0)).
Definition term41 (x0 : nat) := fun y0 : nat => (Nat.mul x0 (Nat.add (NUMERAL 0) y0)) = (Nat.add (Nat.mul x0 (NUMERAL 0)) (Nat.mul x0 y0)).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x1 (Nat.mul x1 x0)) (Nat.mul x1 x2).
Definition term36 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 x1).
Definition term45 (x0 : Prop) := forall y0 : nat, x0.
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term34 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.add (NUMERAL 0) x1).
Definition term24 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.mul x0 (Nat.add y1 y2)) = (Nat.add (Nat.mul x0 y1) (Nat.mul x0 y2))) y0.
Definition term27 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term66 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term2 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (S x0)) (Nat.mul x1 x2).
Definition term14 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) -> forall y0 : nat, (Nat.mul x1 (Nat.add (S x0) y0)) = (Nat.add (Nat.mul x1 (S x0)) (Nat.mul x1 y0)).
