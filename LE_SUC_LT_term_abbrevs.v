Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term56 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term4 (x0 : nat) := Peano.le (S x0) (NUMERAL 0).
Definition term7 (x0 : nat) := and ((Peano.le (S x0) (NUMERAL 0)) = (Peano.lt x0 (NUMERAL 0))).
Definition term3 (x0 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) (NUMERAL 0).
Definition term39 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term26 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) y0.
Definition term21 (x0 : nat) := ((fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) y0) -> (fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) (S y0)).
Definition term15 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) x1) -> (fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) (S x1).
Definition term1 (x0 : nat) := (((fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) y0) -> (fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) y0.
Definition term32 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term55 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (S x0) (S x1)).
Definition term23 (x0 : nat) := imp (((fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) y0) -> (fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) (S y0))).
Definition term22 (x0 : nat) := ((Peano.le (S x0) (NUMERAL 0)) = (Peano.lt x0 (NUMERAL 0))) /\ (forall y0 : nat, ((Peano.le (S x0) y0) = (Peano.lt x0 y0)) -> (Peano.le (S x0) (S y0)) = (Peano.lt x0 (S y0))).
Definition term19 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) y0) -> (fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) (S y0).
Definition term45 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term6 (x0 : nat) := and ((fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) (NUMERAL 0)).
Definition term33 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term27 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term17 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) y0) -> (fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) (S y0).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) x1.
Definition term57 := forall y0 : nat, forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1).
Definition term46 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term41 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term37 (x0 : nat) := @eq Prop (Peano.le (S x0) (NUMERAL 0)).
Definition term52 (x0 : nat) (x1 : nat) := ((S x0) = (S x1)) \/ (Peano.le (S x0) x1).
Definition term14 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term10 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) x1).
Definition term48 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term43 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term28 (x0 : nat) := (((Peano.le (S x0) (NUMERAL 0)) = (Peano.lt x0 (NUMERAL 0))) /\ (forall y0 : nat, ((Peano.le (S x0) y0) = (Peano.lt x0 y0)) -> (Peano.le (S x0) (S y0)) = (Peano.lt x0 (S y0)))) -> forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term30 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term18 (x0 : nat) := fun y0 : nat => ((Peano.le (S x0) y0) = (Peano.lt x0 y0)) -> (Peano.le (S x0) (S y0)) = (Peano.lt x0 (S y0)).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) (S x1).
Definition term44 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term16 (x0 : nat) (x1 : nat) := ((Peano.le (S x0) x1) = (Peano.lt x0 x1)) -> (Peano.le (S x0) (S x1)) = (Peano.lt x0 (S x1)).
Definition term5 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term11 (x0 : nat) (x1 : nat) := imp ((Peano.le (S x0) x1) = (Peano.lt x0 x1)).
Definition term51 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term47 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term38 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term29 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term53 (x0 : nat) (x1 : nat) := or ((S x0) = (S x1)).
Definition term34 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term9 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term31 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term24 (x0 : nat) := imp (((Peano.le (S x0) (NUMERAL 0)) = (Peano.lt x0 (NUMERAL 0))) /\ (forall y0 : nat, ((Peano.le (S x0) y0) = (Peano.lt x0 y0)) -> (Peano.le (S x0) (S y0)) = (Peano.lt x0 (S y0)))).
Definition term25 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le (S x0) y1) = (Peano.lt x0 y1)) y0.
Definition term20 (x0 : nat) := forall y0 : nat, ((Peano.le (S x0) y0) = (Peano.lt x0 y0)) -> (Peano.le (S x0) (S y0)) = (Peano.lt x0 (S y0)).
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term13 (x0 : nat) (x1 : nat) := Peano.le (S x0) (S x1).
Definition term40 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term36 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term50 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term54 (x0 : nat) (x1 : nat) := or (x0 = x1).
