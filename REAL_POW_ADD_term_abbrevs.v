Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term65 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0))) x2.
Definition term51 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term37 (x0 : real) := real_mul (real_pow x0 (NUMERAL 0)).
Definition term73 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_pow x0 (Nat.add (S x1) x2)).
Definition term76 (x0 : real) (x1 : nat) := real_mul (real_mul x0 (real_pow x0 x1)).
Definition term44 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (x0 : real) := forall y0 : nat, (forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) -> forall y1 : nat, (real_pow x0 (Nat.add (S y0) y1)) = (real_mul (real_pow x0 (S y0)) (real_pow x0 y1)).
Definition term53 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term58 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term11 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) (S x1).
Definition term26 (x0 : real) := ((forall y0 : nat, (real_pow x0 (Nat.add (NUMERAL 0) y0)) = (real_mul (real_pow x0 (NUMERAL 0)) (real_pow x0 y0))) /\ (forall y0 : nat, (forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) -> forall y1 : nat, (real_pow x0 (Nat.add (S y0) y1)) = (real_mul (real_pow x0 (S y0)) (real_pow x0 y1)))) -> forall y0 : nat, forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1)).
Definition term56 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term33 (x0 : real) (x1 : nat) := @eq real (real_pow x0 (Nat.add (NUMERAL 0) x1)).
Definition term55 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term54 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term68 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.add (S x1) x2).
Definition term1 (x0 : real) := (((fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) y0) -> (fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) y0.
Definition term35 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term74 (x0 : nat) (x1 : real) (x2 : nat) := @eq real (real_mul (real_mul x1 (real_pow x1 x0)) (real_pow x1 x2)).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term61 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term79 := forall y0 : real, forall y1 : nat, forall y2 : nat, (real_pow y0 (Nat.add y1 y2)) = (real_mul (real_pow y0 y1) (real_pow y0 y2)).
Definition term47 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term21 (x0 : real) := imp (((fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) y0) -> (fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) (S y0))).
Definition term50 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2.
Definition term7 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) x1.
Definition term41 (x0 : real) := fun y0 : nat => (real_pow x0 (Nat.add (NUMERAL 0) y0)) = (real_mul (real_pow x0 (NUMERAL 0)) (real_pow x0 y0)).
Definition term17 (x0 : real) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) y0) -> (fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) (S y0).
Definition term66 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.add x1 x2).
Definition term77 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_pow x1 (S x0)) (real_pow x1 x2).
Definition term27 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term62 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term5 (x0 : real) := and ((fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) (NUMERAL 0)).
Definition term10 (x0 : nat) (x1 : real) := imp (forall y0 : nat, (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0))).
Definition term6 (x0 : real) := and (forall y0 : nat, (real_pow x0 (Nat.add (NUMERAL 0) y0)) = (real_mul (real_pow x0 (NUMERAL 0)) (real_pow x0 y0))).
Definition term49 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term3 (x0 : real) := (fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) (NUMERAL 0).
Definition term31 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term22 (x0 : real) := imp ((forall y0 : nat, (real_pow x0 (Nat.add (NUMERAL 0) y0)) = (real_mul (real_pow x0 (NUMERAL 0)) (real_pow x0 y0))) /\ (forall y0 : nat, (forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) -> forall y1 : nat, (real_pow x0 (Nat.add (S y0) y1)) = (real_mul (real_pow x0 (S y0)) (real_pow x0 y1)))).
Definition term64 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term59 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term25 (x0 : real) := forall y0 : nat, forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1)).
Definition term28 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term75 (x0 : real) (x1 : nat) := real_mul (real_pow x0 (S x1)).
Definition term67 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_pow x1 x0) (real_pow x1 x2).
Definition term43 := forall y0 : nat, True.
Definition term29 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term30 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term70 (x0 : real) (x1 : nat) (x2 : nat) := real_mul x0 (real_pow x0 (Nat.add x1 x2)).
Definition term42 := fun y0 : nat => True.
Definition term12 (x0 : nat) (x1 : real) := forall y0 : nat, (real_pow x1 (Nat.add (S x0) y0)) = (real_mul (real_pow x1 (S x0)) (real_pow x1 y0)).
Definition term8 (x0 : nat) (x1 : real) := forall y0 : nat, (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0)).
Definition term4 (x0 : real) := forall y0 : nat, (real_pow x0 (Nat.add (NUMERAL 0) y0)) = (real_mul (real_pow x0 (NUMERAL 0)) (real_pow x0 y0)).
Definition term9 (x0 : real) (x1 : nat) := imp ((fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) x1).
Definition term16 (x0 : real) := fun y0 : nat => (forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) -> forall y1 : nat, (real_pow x0 (Nat.add (S y0) y1)) = (real_mul (real_pow x0 (S y0)) (real_pow x0 y1)).
Definition term15 (x0 : real) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) y0) -> (fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) (S y0).
Definition term48 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1.
Definition term57 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term13 (x0 : real) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) x1) -> (fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) (S x1).
Definition term38 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term20 (x0 : real) := (forall y0 : nat, (real_pow x0 (Nat.add (NUMERAL 0) y0)) = (real_mul (real_pow x0 (NUMERAL 0)) (real_pow x0 y0))) /\ (forall y0 : nat, (forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) -> forall y1 : nat, (real_pow x0 (Nat.add (S y0) y1)) = (real_mul (real_pow x0 (S y0)) (real_pow x0 y1))).
Definition term78 (x0 : nat) (x1 : real) := fun y0 : nat => (real_pow x1 (Nat.add (S x0) y0)) = (real_mul (real_pow x1 (S x0)) (real_pow x1 y0)).
Definition term23 (x0 : real) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) y0.
Definition term71 (x0 : nat) (x1 : real) (x2 : nat) := real_mul x1 (real_mul (real_pow x1 x0) (real_pow x1 x2)).
Definition term60 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term34 (x0 : real) (x1 : nat) := @eq real (real_pow x0 x1).
Definition term72 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_mul x1 (real_pow x1 x0)) (real_pow x1 x2).
Definition term19 (x0 : real) := ((fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) y0) -> (fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) (S y0)).
Definition term39 (x0 : real) (x1 : nat) := real_mul (real_pow x0 (NUMERAL 0)) (real_pow x0 x1).
Definition term36 := real_of_num (NUMERAL (BIT1 0)).
Definition term52 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term32 (x0 : real) (x1 : nat) := real_pow x0 (Nat.add (NUMERAL 0) x1).
Definition term45 (x0 : Prop) := forall y0 : nat, x0.
Definition term24 (x0 : real) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (real_pow x0 (Nat.add y1 y2)) = (real_mul (real_pow x0 y1) (real_pow x0 y2))) y0.
Definition term46 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0.
Definition term63 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term2 (x0 : real) := fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1)).
Definition term40 (x0 : real) (x1 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term14 (x0 : nat) (x1 : real) := (forall y0 : nat, (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0))) -> forall y0 : nat, (real_pow x1 (Nat.add (S x0) y0)) = (real_mul (real_pow x1 (S x0)) (real_pow x1 y0)).
Definition term69 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (S (Nat.add x1 x2)).
