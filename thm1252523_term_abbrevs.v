Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term30 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x0 (Nat.add x1 (S x2))).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x2 (Nat.add (Nat.add x1 x2) (S x3))).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.add (Nat.add x0 x2) x1) = (Nat.add (Nat.add x0 (Nat.add x1 x3)) (Nat.add (Nat.add x2 x3) (S x4)))) -> False.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x2 (Nat.add x0 (Nat.add (Nat.add x1 x2) (S x3))).
Definition term37 (x0 : nat) (x1 : nat) := imp ((Nat.add x0 (Nat.add x0 (S x1))) = (NUMERAL 0)).
Definition term33 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq nat (Nat.add (Nat.add x0 (Nat.add x1 x3)) (Nat.add (Nat.add x2 x3) (S x4))).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x1 (Nat.add x0 (Nat.add x1 (Nat.add x2 (S x3)))).
Definition term32 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := imp ((Nat.add (Nat.add x0 x2) x1) = (Nat.add (Nat.add x0 (Nat.add x1 x3)) (Nat.add (Nat.add x2 x3) (S x4)))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 (S x2)).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x2 (Nat.add x2 (S x3)))).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x2 (Nat.add x3 (Nat.add x3 (S x4))))).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x1 (Nat.add x2 (Nat.add x3 (S x4))))).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x2 (Nat.add x2 (Nat.add x3 (S x4))))).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x1 (Nat.add x2 (S x3)))).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add x0 (Nat.add x1 x2)).
Definition term31 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add (Nat.add x0 (Nat.add x1 x3)) (Nat.add (Nat.add x2 x3) (S x4)).
Definition term39 (x0 : nat) (x1 : nat) := ((Nat.add x0 (Nat.add x0 (S x1))) = (NUMERAL 0)) -> False.
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.add x0 x1) x2).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x0 (Nat.add x1 (Nat.add x2 (S x3)))).
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = (Nat.add x0 y0)) = (y0 = (NUMERAL 0))) x1.
Definition term25 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x0 (S x1)).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add x0 x2) (Nat.add (Nat.add x1 x2) (S x3)).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x1 (S x2))).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x2 (S x3))).
Definition term27 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = (Nat.add y0 y1)) = (y1 = (NUMERAL 0))) x0.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop ((Nat.add (Nat.add x0 x2) x1) = (Nat.add (Nat.add x0 (Nat.add x1 x3)) (Nat.add (Nat.add x2 x3) (S x4)))).
Definition term28 (x0 : nat) := forall y0 : nat, (x0 = (Nat.add x0 y0)) = (y0 = (NUMERAL 0)).
Definition term13 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x1 (Nat.add x0 (Nat.add x1 (S x2))).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Nat.add x0 (Nat.add (Nat.add x1 x3) (Nat.add (Nat.add x2 x3) (S x4))).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) (S x2).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq nat (Nat.add x0 (Nat.add x1 (Nat.add x1 (Nat.add x2 (Nat.add x3 (S x4)))))).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add x0 (Nat.add (Nat.add x1 x2) (S x3)).
