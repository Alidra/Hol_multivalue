Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : nadd) (x1 : nadd) := dest_nadd (nadd_mul x0 x1).
Definition term6 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_mul y0 y1) = (mk_nadd (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2)))) x0.
Definition term24 (x0 : nadd) (x1 : nadd) := fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0.
Definition term39 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (mk_nadd (fun y0 : nat => dest_nadd x0 (dest_nadd x1 (dest_nadd x2 y0)))) (mk_nadd (fun y0 : nat => dest_nadd x0 (dest_nadd x1 (dest_nadd x2 y0)))).
Definition term17 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (mk_nadd (fun y0 : nat => dest_nadd x0 (dest_nadd (nadd_mul x1 x2) y0))) (mk_nadd (fun y0 : nat => dest_nadd (nadd_mul x0 x1) (dest_nadd x2 y0))).
Definition term33 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := dest_nadd (nadd_mul x0 x1) (dest_nadd x2 x3).
Definition term31 (x0 : nadd) (x1 : nadd) (x2 : nadd) := mk_nadd (fun y0 : nat => dest_nadd x0 (dest_nadd x1 (dest_nadd x2 y0))).
Definition term42 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, nadd_eq (nadd_mul y0 (nadd_mul y1 y2)) (nadd_mul (nadd_mul y0 y1) y2).
Definition term41 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul x0 (nadd_mul y0 y1)) (nadd_mul (nadd_mul x0 y0) y1).
Definition term40 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, nadd_eq (nadd_mul x0 (nadd_mul x1 y0)) (nadd_mul (nadd_mul x0 x1) y0).
Definition term27 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := dest_nadd x0 (dest_nadd (nadd_mul x1 x2) x3).
Definition term34 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := (fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)) (dest_nadd x2 x3).
Definition term26 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)) x2).
Definition term37 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := @eq nat ((fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)) (dest_nadd x2 x3)).
Definition term18 (x0 : nadd) (x1 : nadd) (x2 : nat) := dest_nadd (nadd_mul x0 x1) x2.
Definition term25 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0) x2).
Definition term3 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1))) x1.
Definition term12 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_mul x0 (nadd_mul x1 x2)).
Definition term8 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_mul x0 y0) = (mk_nadd (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1)))) x1.
Definition term36 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0) (dest_nadd x2 x3)).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term0 (x0 : nadd) := (fun y0 : nadd => nadd_eq y0 y0) x0.
Definition term29 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nat => dest_nadd x0 (dest_nadd (nadd_mul x1 x2) y0).
Definition term35 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := (fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0) (dest_nadd x2 x3).
Definition term2 (x0 : nadd) := forall y0 : nadd, (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1)).
Definition term21 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term1 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (dest_nadd (nadd_mul y0 y1)) = (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2))) x0.
Definition term5 (x0 : nadd) (x1 : nadd) := fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0).
Definition term22 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0) x2.
Definition term19 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)) x2.
Definition term9 (x0 : nadd) (x1 : nadd) := mk_nadd (fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)).
Definition term7 (x0 : nadd) := forall y0 : nadd, (nadd_mul x0 y0) = (mk_nadd (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1))).
Definition term16 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_mul x0 (nadd_mul x1 x2)) (nadd_mul (nadd_mul x0 x1) x2).
Definition term11 (x0 : nadd) (x1 : nadd) (x2 : nadd) := mk_nadd (fun y0 : nat => dest_nadd x0 (dest_nadd (nadd_mul x1 x2) y0)).
Definition term10 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_mul x0 (nadd_mul x1 x2).
Definition term14 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_mul (nadd_mul x0 x1) x2.
Definition term30 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nat => dest_nadd x0 (dest_nadd x1 (dest_nadd x2 y0)).
Definition term38 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nat => dest_nadd (nadd_mul x0 x1) (dest_nadd x2 y0).
Definition term32 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (mk_nadd (fun y0 : nat => dest_nadd x0 (dest_nadd x1 (dest_nadd x2 y0)))).
Definition term13 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (mk_nadd (fun y0 : nat => dest_nadd x0 (dest_nadd (nadd_mul x1 x2) y0))).
Definition term23 (x0 : nadd) (x1 : nadd) (x2 : nat) := dest_nadd x0 (dest_nadd x1 x2).
Definition term28 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := dest_nadd x0 (dest_nadd x1 (dest_nadd x2 x3)).
Definition term15 (x0 : nadd) (x1 : nadd) (x2 : nadd) := mk_nadd (fun y0 : nat => dest_nadd (nadd_mul x0 x1) (dest_nadd x2 y0)).
