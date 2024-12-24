Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') := forall y0 : a0, forall y1 : nat -> a0, forall y2 : nat, (@FCONS a0 y0 y1 (S y2)) = (y1 y2).
Definition term29 (a0 : Type') (x0 : nat -> a0) := x0 (NUMERAL 0).
Definition term16 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := (fun y0 : nat -> a0 => (@FCONS a0 x0 y0 (NUMERAL 0)) = x0) x1.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, (@o a0 a1 a2 x0 y0 y1) = (x0 (y0 y1))) x1.
Definition term14 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : nat -> a0, (@FCONS a0 y0 y1 (NUMERAL 0)) = y0) x0.
Definition term51 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, (fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) y0.
Definition term43 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => ((x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) -> (x0 (S y0)) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (S y0)).
Definition term46 (a0 : Type') (x0 : nat -> a0) := ((fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) y0) -> (fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) (S y0)).
Definition term15 (a0 : Type') (x0 : a0) := forall y0 : nat -> a0, (@FCONS a0 x0 y0 (NUMERAL 0)) = x0.
Definition term40 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := ((fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) x1) -> (fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) (S x1).
Definition term13 (a0 : Type') := forall y0 : a0, forall y1 : nat -> a0, (@FCONS a0 y0 y1 (NUMERAL 0)) = y0.
Definition term26 (a0 : Type') (x0 : nat -> a0) := (((fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) y0) -> (fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) y0.
Definition term41 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := ((x0 x1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) x1)) -> (x0 (S x1)) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (S x1)).
Definition term25 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term17 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := @FCONS a0 x0 x1 (NUMERAL 0).
Definition term9 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := (fun y0 : nat -> a0 => forall y1 : nat, (@FCONS a0 x0 y0 (S y1)) = (y0 y1)) x1.
Definition term48 (a0 : Type') (x0 : nat -> a0) := imp (((fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) y0) -> (fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) (S y0))).
Definition term37 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) (S x1).
Definition term27 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0).
Definition term47 (a0 : Type') (x0 : nat -> a0) := ((x0 (NUMERAL 0)) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (NUMERAL 0))) /\ (forall y0 : nat, ((x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) -> (x0 (S y0)) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (S y0))).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (@o a0 a1 a2 x0 x1 y0) = (x0 (x1 y0))) x2.
Definition term38 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := x0 (S x1).
Definition term44 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, ((fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) y0) -> (fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) (S y0).
Definition term33 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) x1.
Definition term31 (a0 : Type') (x0 : nat -> a0) := and ((fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) (NUMERAL 0)).
Definition term34 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) x1.
Definition term22 (a0 : Type') (x0 : nat -> a0) (x1 : nat -> a0) := forall y0 : nat, (x0 y0) = (x1 y0).
Definition term56 (a0 : Type') := forall y0 : nat -> a0, y0 = (@FCONS a0 (y0 (NUMERAL 0)) (@o nat nat a0 y0 S)).
Definition term42 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => ((fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) y0) -> (fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) (S y0).
Definition term53 (a0 : Type') (x0 : nat -> a0) := @eq a0 (x0 (NUMERAL 0)).
Definition term24 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0).
Definition term35 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := imp ((fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) x1).
Definition term52 (a0 : Type') (x0 : nat -> a0) := (((x0 (NUMERAL 0)) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (NUMERAL 0))) /\ (forall y0 : nat, ((x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) -> (x0 (S y0)) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (S y0)))) -> forall y0 : nat, (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) (x2 : a0) := x0 (x1 x2).
Definition term54 (a0 : Type') (x0 : nat -> a0) (x1 : nat -> nat) (x2 : nat) := x0 (x1 x2).
Definition term11 (a0 : Type') (x0 : a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => (@FCONS a0 x0 x1 (S y0)) = (x1 y0)) x2.
Definition term8 (a0 : Type') (x0 : a0) := forall y0 : nat -> a0, forall y1 : nat, (@FCONS a0 x0 y0 (S y1)) = (y0 y1).
Definition term36 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := imp ((x0 x1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) x1)).
Definition term39 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (S x1).
Definition term23 (a0 : Type') (x0 : nat -> a0) := @FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := forall y0 : a0, (@o a0 a1 a2 x0 x1 y0) = (x0 (x1 y0)).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) := (fun y0 : a1 -> a2 => forall y1 : a0 -> a1, forall y2 : a0, (@o a0 a1 a2 y0 y1 y2) = (y0 (y1 y2))) x0.
Definition term30 (a0 : Type') (x0 : nat -> a0) := @FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (NUMERAL 0).
Definition term49 (a0 : Type') (x0 : nat -> a0) := imp (((x0 (NUMERAL 0)) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (NUMERAL 0))) /\ (forall y0 : nat, ((x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) -> (x0 (S y0)) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (S y0)))).
Definition term50 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => (fun y1 : nat => (x0 y1) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y1)) y0.
Definition term45 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, ((x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) -> (x0 (S y0)) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (S y0)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term55 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @eq a0 (x0 (S x1)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term32 (a0 : Type') (x0 : nat -> a0) := and ((x0 (NUMERAL 0)) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) (NUMERAL 0))).
Definition term28 (a0 : Type') (x0 : nat -> a0) := (fun y0 : nat => (x0 y0) = (@FCONS a0 (x0 (NUMERAL 0)) (@o nat nat a0 x0 S) y0)) (NUMERAL 0).
Definition term7 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : nat -> a0, forall y2 : nat, (@FCONS a0 y0 y1 (S y2)) = (y1 y2)) x0.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) := forall y0 : a0 -> a1, forall y1 : a0, (@o a0 a1 a2 x0 y0 y1) = (x0 (y0 y1)).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term10 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := forall y0 : nat, (@FCONS a0 x0 x1 (S y0)) = (x1 y0).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term12 (a0 : Type') (x0 : a0) (x1 : nat -> a0) (x2 : nat) := @FCONS a0 x0 x1 (S x2).
