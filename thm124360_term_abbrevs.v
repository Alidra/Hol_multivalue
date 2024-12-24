Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term52 := fun y0 : type1307 => forall y1 : type1674, ((y0 y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y0 y1 (S y2)) = (~ (y0 y1 y2))).
Definition term43 := @eq Prop (forall y0 : type1674, exists y1 : nat -> Prop, ((y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y1 (S y2)) = (~ (y1 y2)))).
Definition term42 := @eq Prop (forall y0 : type1674, exists y1 : nat -> Prop, (fun y2 : type1674 => fun y3 : nat -> Prop => ((y3 (NUMERAL 0)) = False) /\ (forall y4 : nat, (y3 (S y4)) = (~ (y3 y4)))) y0 y1).
Definition term4 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term51 := fun y0 : type1307 => forall y1 : type1674, (fun y2 : type1674 => fun y3 : nat -> Prop => ((y3 (NUMERAL 0)) = False) /\ (forall y4 : nat, (y3 (S y4)) = (~ (y3 y4)))) y1 (y0 y1).
Definition term38 (x0 : type1674) := fun y0 : nat -> Prop => (fun y1 : type1674 => fun y2 : nat -> Prop => ((y2 (NUMERAL 0)) = False) /\ (forall y3 : nat, (y2 (S y3)) = (~ (y2 y3)))) x0 y0.
Definition term21 (x0 : nat -> Prop) := and ((x0 (NUMERAL 0)) = False).
Definition term36 (x0 : type1674) (x1 : nat -> Prop) := (fun y0 : type1674 => fun y1 : nat -> Prop => ((y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y1 (S y2)) = (~ (y1 y2)))) x0 x1.
Definition term16 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 x1)) x1.
Definition term8 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := (fun y0 : type1423 a0 => exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) x1.
Definition term57 := (fun y0 : type1307 => forall y1 : type1674, ((y0 y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y0 y1 (S y2)) = (~ (y0 y1 y2)))) (@ε ((prod nat (prod nat nat)) -> nat -> Prop) (fun y0 : type1307 => forall y1 : type1674, ((y0 y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y0 y1 (S y2)) = (~ (y0 y1 y2))))).
Definition term24 := fun y0 : nat -> Prop => ((y0 (NUMERAL 0)) = False) /\ (forall y1 : nat, (y0 (S y1)) = (~ (y0 y1))).
Definition term23 := fun y0 : nat -> Prop => ((y0 (NUMERAL 0)) = False) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : Prop => fun y3 : nat => ~ y2) (y0 y1) y1)).
Definition term20 (x0 : nat -> Prop) := forall y0 : nat, (x0 (S y0)) = ((fun y1 : Prop => fun y2 : nat => ~ y1) (x0 y0) y0).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term53 := exists y0 : type1307, forall y1 : type1674, ((y0 y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y0 y1 (S y2)) = (~ (y0 y1 y2))).
Definition term33 := exists y0 : type1307, forall y1 : type1674, (fun y2 : type1674 => fun y3 : nat -> Prop => ((y3 (NUMERAL 0)) = False) /\ (forall y4 : nat, (y3 (S y4)) = (~ (y3 y4)))) y1 (y0 y1).
Definition term31 (x0 : type1301) := exists y0 : type1307, forall y1 : type1674, x0 y1 (y0 y1).
Definition term49 (x0 : type1307) := forall y0 : type1674, (fun y1 : type1674 => fun y2 : nat -> Prop => ((y2 (NUMERAL 0)) = False) /\ (forall y3 : nat, (y2 (S y3)) = (~ (y2 y3)))) y0 (x0 y0).
Definition term17 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (x0 (S x1)).
Definition term50 (x0 : type1307) := forall y0 : type1674, ((x0 y0 (NUMERAL 0)) = False) /\ (forall y1 : nat, (x0 y0 (S y1)) = (~ (x0 y0 y1))).
Definition term55 := fun y0 : type370 => y0 (@ε ((prod nat (prod nat nat)) -> nat -> Prop) y0).
Definition term18 (x0 : nat -> Prop) := fun y0 : nat => (x0 (S y0)) = ((fun y1 : Prop => fun y2 : nat => ~ y1) (x0 y0) y0).
Definition term6 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1423 a0, exists y2 : nat -> a0, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) x0.
Definition term37 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => ((y0 (NUMERAL 0)) = False) /\ (forall y1 : nat, (y0 (S y1)) = (~ (y0 y1)))) x0.
Definition term2 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 (S y0)) = (~ (x0 y0))) x1.
Definition term12 := fun y0 : Prop => fun y1 : nat => ~ y0.
Definition term34 := fun y0 : type1674 => fun y1 : nat -> Prop => ((y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y1 (S y2)) = (~ (y1 y2))).
Definition term41 := fun y0 : type1674 => exists y1 : nat -> Prop, ((y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y1 (S y2)) = (~ (y1 y2))).
Definition term48 (x0 : type1307) := fun y0 : type1674 => ((x0 y0 (NUMERAL 0)) = False) /\ (forall y1 : nat, (x0 y0 (S y1)) = (~ (x0 y0 y1))).
Definition term54 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term44 (x0 : type1307) (x1 : type1674) := (fun y0 : type1674 => fun y1 : nat -> Prop => ((y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y1 (S y2)) = (~ (y1 y2)))) x1 (x0 x1).
Definition term56 := (fun y0 : type370 => y0 (@ε ((prod nat (prod nat nat)) -> nat -> Prop) y0)) (fun y0 : type1307 => forall y1 : type1674, ((y0 y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y0 y1 (S y2)) = (~ (y0 y1 y2)))).
Definition term1 (x0 : nat -> Prop) := forall y0 : nat, (x0 (S y0)) = (~ (x0 y0)).
Definition term14 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ~ (x0 x1).
Definition term22 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) = False) /\ (forall y0 : nat, (x0 (S y0)) = ((fun y1 : Prop => fun y2 : nat => ~ y1) (x0 y0) y0)).
Definition term5 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) = False) /\ (forall y0 : nat, (x0 (S y0)) = (~ (x0 y0))).
Definition term46 (x0 : type1307) (x1 : type1674) := ((x0 x1 (NUMERAL 0)) = False) /\ (forall y0 : nat, (x0 x1 (S y0)) = (~ (x0 x1 y0))).
Definition term39 (x0 : type1674) := exists y0 : nat -> Prop, (fun y1 : type1674 => fun y2 : nat -> Prop => ((y2 (NUMERAL 0)) = False) /\ (forall y3 : nat, (y2 (S y3)) = (~ (y2 y3)))) x0 y0.
Definition term19 (x0 : nat -> Prop) := fun y0 : nat => (x0 (S y0)) = (~ (x0 y0)).
Definition term13 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : Prop => fun y1 : nat => ~ y0) (x0 x1).
Definition term25 := exists y0 : nat -> Prop, ((y0 (NUMERAL 0)) = False) /\ (forall y1 : nat, (y0 (S y1)) = (~ (y0 y1))).
Definition term11 := exists y0 : nat -> Prop, ((y0 (NUMERAL 0)) = False) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : Prop => fun y3 : nat => ~ y2) (y0 y1) y1)).
Definition term47 (x0 : type1307) := fun y0 : type1674 => (fun y1 : type1674 => fun y2 : nat -> Prop => ((y2 (NUMERAL 0)) = False) /\ (forall y3 : nat, (y2 (S y3)) = (~ (y2 y3)))) y0 (x0 y0).
Definition term0 (x0 : nat -> Prop) := x0 (NUMERAL 0).
Definition term45 (x0 : type1307) (x1 : type1674) := (fun y0 : nat -> Prop => ((y0 (NUMERAL 0)) = False) /\ (forall y1 : nat, (y0 (S y1)) = (~ (y0 y1)))) (x0 x1).
Definition term3 (x0 : nat -> Prop) (x1 : nat) := x0 (S x1).
Definition term7 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term35 (x0 : type1674) := (fun y0 : type1674 => fun y1 : nat -> Prop => ((y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y1 (S y2)) = (~ (y1 y2)))) x0.
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term10 (x0 : Prop) (x1 : type1544) := exists y0 : nat -> Prop, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term9 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term32 := forall y0 : type1674, exists y1 : nat -> Prop, (fun y2 : type1674 => fun y3 : nat -> Prop => ((y3 (NUMERAL 0)) = False) /\ (forall y4 : nat, (y3 (S y4)) = (~ (y3 y4)))) y0 y1.
Definition term30 (x0 : type1301) := forall y0 : type1674, exists y1 : nat -> Prop, x0 y0 y1.
Definition term15 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : Prop => fun y1 : nat => ~ y0) (x0 x1) x1.
Definition term26 := forall y0 : type1674, exists y1 : nat -> Prop, ((y1 (NUMERAL 0)) = False) /\ (forall y2 : nat, (y1 (S y2)) = (~ (y1 y2))).
Definition term40 := fun y0 : type1674 => exists y1 : nat -> Prop, (fun y2 : type1674 => fun y3 : nat -> Prop => ((y3 (NUMERAL 0)) = False) /\ (forall y4 : nat, (y3 (S y4)) = (~ (y3 y4)))) y0 y1.
