Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term39 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub x0 (S y0)) = (Nat.pred (Nat.sub x0 y0))) x1.
Definition term40 (x0 : nat) (x1 : nat) := Nat.pred (Nat.sub x0 x1).
Definition term16 (x0 : nat) (x1 : nat) := ((Nat.pred (Nat.sub (S x0) x1)) = (Nat.sub x0 x1)) -> (Nat.pred (Nat.sub (S x0) (S x1))) = (Nat.sub x0 (S x1)).
Definition term27 (x0 : nat) := forall y0 : nat, (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0).
Definition term14 (x0 : nat) (x1 : nat) := Nat.sub x0 (S x1).
Definition term43 (x0 : nat) (x1 : nat) := @eq nat (Nat.pred (Nat.sub x0 x1)).
Definition term4 (x0 : nat) := Nat.pred (Nat.sub (S x0) (NUMERAL 0)).
Definition term26 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) y0.
Definition term21 (x0 : nat) := ((fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) y0) -> (fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) (S y0)).
Definition term33 (x0 : nat) := (fun y0 : nat => (Nat.sub y0 (NUMERAL 0)) = y0) x0.
Definition term15 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) x1) -> (fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) (S x1).
Definition term38 (x0 : nat) := forall y0 : nat, (Nat.sub x0 (S y0)) = (Nat.pred (Nat.sub x0 y0)).
Definition term1 (x0 : nat) := (((fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) y0) -> (fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) y0.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term23 (x0 : nat) := imp (((fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) y0) -> (fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) (S y0))).
Definition term19 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) y0) -> (fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) (S y0).
Definition term32 := forall y0 : nat, (Nat.sub y0 (NUMERAL 0)) = y0.
Definition term13 (x0 : nat) (x1 : nat) := Nat.pred (Nat.sub (S x0) (S x1)).
Definition term6 (x0 : nat) := and ((fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) (NUMERAL 0)).
Definition term35 (x0 : nat) := @eq nat (Nat.pred (Nat.sub (S x0) (NUMERAL 0))).
Definition term17 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) y0) -> (fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) (S y0).
Definition term7 (x0 : nat) := and ((Nat.pred (Nat.sub (S x0) (NUMERAL 0))) = (Nat.sub x0 (NUMERAL 0))).
Definition term44 := forall y0 : nat, forall y1 : nat, (Nat.pred (Nat.sub (S y0) y1)) = (Nat.sub y0 y1).
Definition term36 := forall y0 : nat, forall y1 : nat, (Nat.sub y0 (S y1)) = (Nat.pred (Nat.sub y0 y1)).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) (S x1).
Definition term42 (x0 : nat) (x1 : nat) := @eq nat (Nat.pred (Nat.sub (S x0) (S x1))).
Definition term10 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) x1).
Definition term28 (x0 : nat) := (((Nat.pred (Nat.sub (S x0) (NUMERAL 0))) = (Nat.sub x0 (NUMERAL 0))) /\ (forall y0 : nat, ((Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) -> (Nat.pred (Nat.sub (S x0) (S y0))) = (Nat.sub x0 (S y0)))) -> forall y0 : nat, (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0).
Definition term34 (x0 : nat) := Nat.sub (S x0) (NUMERAL 0).
Definition term29 := forall y0 : nat, (Nat.pred (S y0)) = y0.
Definition term18 (x0 : nat) := fun y0 : nat => ((Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) -> (Nat.pred (Nat.sub (S x0) (S y0))) = (Nat.sub x0 (S y0)).
Definition term5 (x0 : nat) := Nat.sub x0 (NUMERAL 0).
Definition term11 (x0 : nat) (x1 : nat) := imp ((Nat.pred (Nat.sub (S x0) x1)) = (Nat.sub x0 x1)).
Definition term41 (x0 : nat) (x1 : nat) := Nat.sub (S x0) (S x1).
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub y0 (S y1)) = (Nat.pred (Nat.sub y0 y1))) x0.
Definition term9 (x0 : nat) (x1 : nat) := Nat.pred (Nat.sub (S x0) x1).
Definition term24 (x0 : nat) := imp (((Nat.pred (Nat.sub (S x0) (NUMERAL 0))) = (Nat.sub x0 (NUMERAL 0))) /\ (forall y0 : nat, ((Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) -> (Nat.pred (Nat.sub (S x0) (S y0))) = (Nat.sub x0 (S y0)))).
Definition term25 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.pred (Nat.sub (S x0) y1)) = (Nat.sub x0 y1)) y0.
Definition term22 (x0 : nat) := ((Nat.pred (Nat.sub (S x0) (NUMERAL 0))) = (Nat.sub x0 (NUMERAL 0))) /\ (forall y0 : nat, ((Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) -> (Nat.pred (Nat.sub (S x0) (S y0))) = (Nat.sub x0 (S y0))).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) x1.
Definition term20 (x0 : nat) := forall y0 : nat, ((Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) -> (Nat.pred (Nat.sub (S x0) (S y0))) = (Nat.sub x0 (S y0)).
Definition term3 (x0 : nat) := (fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0)) (NUMERAL 0).
Definition term30 (x0 : nat) := (fun y0 : nat => (Nat.pred (S y0)) = y0) x0.
Definition term2 (x0 : nat) := fun y0 : nat => (Nat.pred (Nat.sub (S x0) y0)) = (Nat.sub x0 y0).
Definition term31 (x0 : nat) := Nat.pred (S x0).
