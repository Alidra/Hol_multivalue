Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 := hreal_of_num (NUMERAL 0).
Definition term12 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add x2 y0))) x3.
Definition term10 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_le (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add y0 y1))) x2.
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term30 (x0 : nat) := forall y0 : nat, (treal_le (treal_of_num x0) (treal_of_num y0)) = (Peano.le x0 y0).
Definition term3 (x0 : nat) := forall y0 : nat, (hreal_le (hreal_of_num x0) (hreal_of_num y0)) = (Peano.le x0 y0).
Definition term23 (x0 : nat) := hreal_add (hreal_of_num x0) (hreal_of_num (NUMERAL 0)).
Definition term28 (x0 : nat) := fun y0 : nat => (treal_le (treal_of_num x0) (treal_of_num y0)) = (Peano.le x0 y0).
Definition term14 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add x0 x1) (hreal_add x2 x3).
Definition term8 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_le (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = (hreal_le (hreal_add x0 y0) (hreal_add y1 y2))) x1.
Definition term34 := fun y0 : nat => forall y1 : nat, (treal_le (treal_of_num y0) (treal_of_num y1)) = (Peano.le y0 y1).
Definition term1 (x0 : hreal) := hreal_add x0 (hreal_of_num (NUMERAL 0)).
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (hreal_le (hreal_of_num x0) (hreal_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term5 (x0 : nat) (x1 : nat) := hreal_le (hreal_of_num x0) (hreal_of_num x1).
Definition term24 (x0 : nat) := hreal_le (hreal_add (hreal_of_num x0) (hreal_of_num (NUMERAL 0))).
Definition term9 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_le (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add y0 y1)).
Definition term7 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_le (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = (hreal_le (hreal_add x0 y0) (hreal_add y1 y2)).
Definition term16 (x0 : nat) := @pair hreal hreal (hreal_of_num x0) (hreal_of_num (NUMERAL 0)).
Definition term35 := forall y0 : nat, forall y1 : nat, (treal_le (treal_of_num y0) (treal_of_num y1)) = (Peano.le y0 y1).
Definition term26 (x0 : nat) (x1 : nat) := @eq Prop (treal_le (treal_of_num x0) (treal_of_num x1)).
Definition term31 := forall y0 : nat, True.
Definition term25 (x0 : nat) := hreal_le (hreal_of_num x0).
Definition term29 := fun y0 : nat => True.
Definition term17 (x0 : nat) := treal_le (treal_of_num x0).
Definition term21 (x0 : nat) (x1 : nat) := hreal_le (hreal_add (hreal_of_num x0) (hreal_of_num (NUMERAL 0))) (hreal_add (hreal_of_num x1) (hreal_of_num (NUMERAL 0))).
Definition term0 (x0 : hreal) := (fun y0 : hreal => (hreal_add y0 (hreal_of_num (NUMERAL 0))) = y0) x0.
Definition term27 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term19 (x0 : nat) (x1 : nat) := treal_le (treal_of_num x0) (treal_of_num x1).
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (hreal_le (hreal_of_num y0) (hreal_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term18 (x0 : nat) := treal_le (@pair hreal hreal (hreal_of_num x0) (hreal_of_num (NUMERAL 0))).
Definition term13 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_le (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term15 (x0 : nat) := (fun y0 : nat => (treal_of_num y0) = (@pair hreal hreal (hreal_of_num y0) (hreal_of_num (NUMERAL 0)))) x0.
Definition term11 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add x2 y0)).
Definition term33 (x0 : Prop) := forall y0 : nat, x0.
Definition term20 (x0 : nat) (x1 : nat) := treal_le (@pair hreal hreal (hreal_of_num x0) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num x1) (hreal_of_num (NUMERAL 0))).
Definition term6 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_le (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = (hreal_le (hreal_add y0 y1) (hreal_add y2 y3))) x0.