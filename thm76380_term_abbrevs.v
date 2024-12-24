Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term30 := @eq nat (@ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) (NUMERAL 0)).
Definition term37 (x0 : nat) := @eq nat (BIT0 (S x0)).
Definition term33 := and ((BIT0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term7 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => S (S (x0 x1)).
Definition term35 (x0 : nat) := BIT0 (S x0).
Definition term4 := fun y0 : nat => fun y1 : nat => S (S y0).
Definition term14 (x0 : nat -> nat) := fun y0 : nat => (x0 (S y0)) = (S (S (x0 y0))).
Definition term10 (x0 : nat -> nat) (x1 : nat) := S (S (x0 x1)).
Definition term41 (x0 : nat) := S (S (@ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) x0)).
Definition term3 := (fun y0 : type1606 => exists y1 : nat -> nat, ((y1 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) (fun y0 : nat => fun y1 : nat => S (S y0)).
Definition term15 (x0 : nat -> nat) := forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat => fun y2 : nat => S (S y1)) (x0 y0) y0).
Definition term24 := (exists y0 : nat -> nat, ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) -> (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) (@ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1)))))).
Definition term6 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => S (S y0)) (x0 x1).
Definition term21 := fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1)))).
Definition term20 := fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat => fun y3 : nat => S (S y2)) (y0 y1) y1)).
Definition term22 := exists y0 : nat -> nat, ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1)))).
Definition term5 := exists y0 : nat -> nat, ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat => fun y3 : nat => S (S y2)) (y0 y1) y1)).
Definition term13 (x0 : nat -> nat) := fun y0 : nat => (x0 (S y0)) = ((fun y1 : nat => fun y2 : nat => S (S y1)) (x0 y0) y0).
Definition term26 := ((@ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, (@ε (nat -> nat) (fun y1 : nat -> nat => ((y1 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y2 : nat, (y1 (S y2)) = (S (S (y1 y2))))) (S y0)) = (S (S (@ε (nat -> nat) (fun y1 : nat -> nat => ((y1 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y2 : nat, (y1 (S y2)) = (S (S (y1 y2))))) y0)))).
Definition term46 := forall y0 : nat, (BIT0 (S y0)) = (S (S (BIT0 y0))).
Definition term32 := and ((@ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) (NUMERAL 0)) = (NUMERAL 0)).
Definition term43 := fun y0 : nat => (@ε (nat -> nat) (fun y1 : nat -> nat => ((y1 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y2 : nat, (y1 (S y2)) = (S (S (y1 y2))))) (S y0)) = (S (S (@ε (nat -> nat) (fun y1 : nat -> nat => ((y1 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y2 : nat, (y1 (S y2)) = (S (S (y1 y2))))) y0))).
Definition term47 := ((BIT0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, (BIT0 (S y0)) = (S (S (BIT0 y0)))).
Definition term25 := (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) (@ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1)))))).
Definition term1 := (fun y0 : nat => forall y1 : type1606, exists y2 : nat -> nat, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) (NUMERAL 0).
Definition term0 := forall y0 : nat, forall y1 : type1606, exists y2 : nat -> nat, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3)).
Definition term19 (x0 : nat -> nat) := ((x0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, (x0 (S y0)) = (S (S (x0 y0)))).
Definition term18 (x0 : nat -> nat) := ((x0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat => fun y2 : nat => S (S y1)) (x0 y0) y0)).
Definition term29 := BIT0 (NUMERAL 0).
Definition term8 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => S (S y0)) (x0 x1) x1.
Definition term11 (x0 : nat -> nat) (x1 : nat) := @eq nat (x0 (S x1)).
Definition term16 (x0 : nat -> nat) := forall y0 : nat, (x0 (S y0)) = (S (S (x0 y0))).
Definition term28 := @ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) (NUMERAL 0).
Definition term23 (x0 : type1002) := (ex x0) -> x0 (@ε (nat -> nat) x0).
Definition term36 (x0 : nat) := @eq nat (@ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) (S x0)).
Definition term42 (x0 : nat) := S (S (BIT0 x0)).
Definition term17 (x0 : nat -> nat) := and ((x0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term38 (x0 : nat) := @ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) x0.
Definition term45 := forall y0 : nat, (@ε (nat -> nat) (fun y1 : nat -> nat => ((y1 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y2 : nat, (y1 (S y2)) = (S (S (y1 y2))))) (S y0)) = (S (S (@ε (nat -> nat) (fun y1 : nat -> nat => ((y1 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y2 : nat, (y1 (S y2)) = (S (S (y1 y2))))) y0))).
Definition term9 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => S (S (x0 x1))) x1.
Definition term34 (x0 : nat) := @ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) (S x0).
Definition term12 (x0 : nat -> nat) (x1 : nat) := x0 (S x1).
Definition term39 (x0 : nat) := S (@ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))) x0).
Definition term27 := @ε (nat -> nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))).
Definition term40 (x0 : nat) := S (BIT0 x0).
Definition term31 := @eq nat (BIT0 (NUMERAL 0)).
Definition term2 := forall y0 : type1606, exists y1 : nat -> nat, ((y1 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term44 := fun y0 : nat => (BIT0 (S y0)) = (S (S (BIT0 y0))).
