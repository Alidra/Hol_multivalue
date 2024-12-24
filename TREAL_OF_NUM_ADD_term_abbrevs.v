Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term32 := hreal_of_num (NUMERAL 0).
Definition term47 (x0 : nat) := forall y0 : nat, treal_eq (treal_add (treal_of_num x0) (treal_of_num y0)) (treal_of_num (Nat.add x0 y0)).
Definition term7 (x0 : nat) (x1 : nat) := hreal_of_num (Nat.add x0 x1).
Definition term15 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_add (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term29 (x0 : nat) (x1 : nat) := treal_add (treal_of_num x0) (treal_of_num x1).
Definition term23 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0))) x3.
Definition term27 (x0 : nat) := treal_add (treal_of_num x0).
Definition term21 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1))) x2.
Definition term12 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_add (@pair hreal hreal x0 y0) (@pair hreal hreal x1 y1)) = (@pair hreal hreal (hreal_add x0 x1) (hreal_add y0 y1))) x2.
Definition term49 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term40 (x0 : nat) (x1 : nat) := treal_eq (@pair hreal hreal (hreal_of_num (Nat.add x0 x1)) (hreal_of_num (NUMERAL 0))).
Definition term28 (x0 : nat) := treal_add (@pair hreal hreal (hreal_of_num x0) (hreal_of_num (NUMERAL 0))).
Definition term4 (x0 : nat) := forall y0 : nat, (hreal_add (hreal_of_num x0) (hreal_of_num y0)) = (hreal_of_num (Nat.add x0 y0)).
Definition term43 (x0 : nat) (x1 : nat) := treal_eq (@pair hreal hreal (hreal_of_num (Nat.add x0 x1)) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (Nat.add x0 x1)) (hreal_of_num (NUMERAL 0))).
Definition term19 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2))) x1.
Definition term10 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_add (@pair hreal hreal x0 y1) (@pair hreal hreal y0 y2)) = (@pair hreal hreal (hreal_add x0 y0) (hreal_add y1 y2))) x1.
Definition term35 := hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0)).
Definition term37 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term30 (x0 : nat) (x1 : nat) := treal_add (@pair hreal hreal (hreal_of_num x0) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num x1) (hreal_of_num (NUMERAL 0))).
Definition term2 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term20 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1)).
Definition term18 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2)).
Definition term11 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_add (@pair hreal hreal x0 y0) (@pair hreal hreal x1 y1)) = (@pair hreal hreal (hreal_add x0 x1) (hreal_add y0 y1)).
Definition term9 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_add (@pair hreal hreal x0 y1) (@pair hreal hreal y0 y2)) = (@pair hreal hreal (hreal_add x0 y0) (hreal_add y1 y2)).
Definition term26 (x0 : nat) := @pair hreal hreal (hreal_of_num x0) (hreal_of_num (NUMERAL 0)).
Definition term52 := forall y0 : nat, forall y1 : nat, treal_eq (treal_add (treal_of_num y0) (treal_of_num y1)) (treal_of_num (Nat.add y0 y1)).
Definition term36 := hreal_of_num (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term33 (x0 : nat) (x1 : nat) := @pair hreal hreal (hreal_add (hreal_of_num x0) (hreal_of_num x1)).
Definition term48 := forall y0 : nat, True.
Definition term0 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term31 (x0 : nat) (x1 : nat) := @pair hreal hreal (hreal_add (hreal_of_num x0) (hreal_of_num x1)) (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))).
Definition term42 (x0 : nat) (x1 : nat) := treal_eq (treal_add (treal_of_num x0) (treal_of_num x1)) (treal_of_num (Nat.add x0 x1)).
Definition term1 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term39 (x0 : nat) (x1 : nat) := treal_eq (treal_add (treal_of_num x0) (treal_of_num x1)).
Definition term6 (x0 : nat) (x1 : nat) := hreal_add (hreal_of_num x0) (hreal_of_num x1).
Definition term46 := fun y0 : nat => True.
Definition term34 (x0 : nat) (x1 : nat) := @pair hreal hreal (hreal_of_num (Nat.add x0 x1)).
Definition term45 (x0 : nat) := fun y0 : nat => treal_eq (treal_add (treal_of_num x0) (treal_of_num y0)) (treal_of_num (Nat.add x0 y0)).
Definition term14 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_add (@pair hreal hreal x0 x2) (@pair hreal hreal x1 y0)) = (@pair hreal hreal (hreal_add x0 x1) (hreal_add x2 y0))) x3.
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (hreal_add (hreal_of_num y0) (hreal_of_num y1)) = (hreal_of_num (Nat.add y0 y1))) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => (treal_of_num y0) = (@pair hreal hreal (hreal_of_num y0) (hreal_of_num (NUMERAL 0)))) x0.
Definition term22 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0)).
Definition term13 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_add (@pair hreal hreal x0 x2) (@pair hreal hreal x1 y0)) = (@pair hreal hreal (hreal_add x0 x1) (hreal_add x2 y0)).
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (hreal_add (hreal_of_num x0) (hreal_of_num y0)) = (hreal_of_num (Nat.add x0 y0))) x1.
Definition term38 (x0 : nat) (x1 : nat) := @pair hreal hreal (hreal_of_num (Nat.add x0 x1)) (hreal_of_num (NUMERAL 0)).
Definition term50 (x0 : Prop) := forall y0 : nat, x0.
Definition term41 (x0 : nat) (x1 : nat) := treal_of_num (Nat.add x0 x1).
Definition term51 := fun y0 : nat => forall y1 : nat, treal_eq (treal_add (treal_of_num y0) (treal_of_num y1)) (treal_of_num (Nat.add y0 y1)).
Definition term16 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @pair hreal hreal (hreal_add x0 x1) (hreal_add x2 x3).
Definition term44 (x0 : nat) (x1 : nat) := hreal_add (hreal_of_num (Nat.add x0 x1)) (hreal_of_num (NUMERAL 0)).
Definition term24 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term17 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_eq (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = ((hreal_add y0 y1) = (hreal_add y2 y3))) x0.
Definition term8 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_add (@pair hreal hreal y0 y2) (@pair hreal hreal y1 y3)) = (@pair hreal hreal (hreal_add y0 y1) (hreal_add y2 y3))) x0.
