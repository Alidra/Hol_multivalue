Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_mul y0 y1) = (mk_nadd (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2)))) x0.
Definition term42 (x0 : nat -> nat) := fun y0 : nat => x0 y0.
Definition term22 (x0 : nadd) (x1 : nat) := dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) (dest_nadd x0 x1).
Definition term4 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term46 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term47 (x0 : Prop) := forall y0 : nadd, x0.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term45 := forall y0 : nadd, True.
Definition term27 (x0 : nat) := (fun y0 : nat => y0) x0.
Definition term28 := fun y0 : nat => (fun y1 : nat => y1) y0.
Definition term33 (x0 : nadd) := mk_nadd (fun y0 : nat => dest_nadd x0 y0).
Definition term17 := nadd_of_num (NUMERAL (BIT1 0)).
Definition term40 := forall y0 : nadd, nadd_eq (nadd_mul (nadd_of_num (NUMERAL (BIT1 0))) y0) y0.
Definition term13 (x0 : nat) := dest_nadd (nadd_of_num x0).
Definition term38 := fun y0 : nadd => nadd_eq (nadd_mul (nadd_of_num (NUMERAL (BIT1 0))) y0) y0.
Definition term15 (x0 : nadd) := nadd_mul (nadd_of_num (NUMERAL (BIT1 0))) x0.
Definition term36 (x0 : nadd) := nadd_eq (nadd_mul (nadd_of_num (NUMERAL (BIT1 0))) x0) x0.
Definition term29 (x0 : nadd) (x1 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => y1) y0) (dest_nadd x0 x1)).
Definition term10 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_mul x0 y0) = (mk_nadd (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1)))) x1.
Definition term18 := dest_nadd (nadd_of_num (NUMERAL (BIT1 0))).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term2 (x0 : nadd) := (fun y0 : nadd => nadd_eq y0 y0) x0.
Definition term21 := fun y0 : nat => y0.
Definition term23 (x0 : nadd) (x1 : nat) := (fun y0 : nat => y0) (dest_nadd x0 x1).
Definition term25 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term5 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term6 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term26 (x0 : nadd) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => y1) y0) (dest_nadd x0 x1).
Definition term43 (x0 : nadd) := mk_nadd (dest_nadd x0).
Definition term11 (x0 : nadd) (x1 : nadd) := mk_nadd (fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)).
Definition term35 (x0 : nadd) := nadd_eq (mk_nadd (fun y0 : nat => dest_nadd x0 y0)).
Definition term14 (x0 : nat) := fun y0 : nat => Nat.mul x0 y0.
Definition term12 (x0 : nat) := (fun y0 : nat => (dest_nadd (nadd_of_num y0)) = (fun y1 : nat => Nat.mul y0 y1)) x0.
Definition term9 (x0 : nadd) := forall y0 : nadd, (nadd_mul x0 y0) = (mk_nadd (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1))).
Definition term31 (x0 : nadd) := fun y0 : nat => dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) (dest_nadd x0 y0).
Definition term34 (x0 : nadd) := nadd_eq (nadd_mul (nadd_of_num (NUMERAL (BIT1 0))) x0).
Definition term44 := fun y0 : nadd => True.
Definition term19 := fun y0 : nat => Nat.mul (NUMERAL (BIT1 0)) y0.
Definition term37 (x0 : nadd) := nadd_eq (mk_nadd (fun y0 : nat => dest_nadd x0 y0)) x0.
Definition term32 (x0 : nadd) := fun y0 : nat => dest_nadd x0 y0.
Definition term30 (x0 : nadd) (x1 : nat) := @eq nat ((fun y0 : nat => y0) (dest_nadd x0 x1)).
Definition term41 := forall y0 : nadd, nadd_eq (mk_nadd (fun y1 : nat => dest_nadd y0 y1)) y0.
Definition term39 := fun y0 : nadd => nadd_eq (mk_nadd (fun y1 : nat => dest_nadd y0 y1)) y0.
Definition term3 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term16 (x0 : nadd) := mk_nadd (fun y0 : nat => dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) (dest_nadd x0 y0)).
Definition term20 := NUMERAL (BIT1 0).
Definition term7 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
