Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (((forall y0 : a0, (~ (@IN a0 y0 x2)) -> (x0 y0) = (@ARB a1)) /\ (~ (@IN a0 x1 x2))) -> ((x0 x1) = (@ARB a1)) = x3) -> (((@IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 x2)) /\ (~ (@IN a0 x1 x2))) -> (x0 x1) = (@ARB a1)) = (((forall y0 : a0, (~ (@IN a0 y0 x2)) -> (x0 y0) = (@ARB a1)) /\ (~ (@IN a0 x1 x2))) -> x3).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, (~ (@IN a0 y0 x0)) -> (x1 y0) = (@ARB a1).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := ((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) -> (x1 x2) = (@ARB a1).
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term40 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, forall y2 : a0, ((@IN (a0 -> a1) y1 (@EXTENSIONAL a0 a1 y0)) /\ (~ (@IN a0 y2 y0))) -> (y1 y2) = (@ARB a1).
Definition term31 (a0 : Type') := forall y0 : a0, True.
Definition term42 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term37 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, x0.
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) := (@IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 x2)) /\ (~ (@IN a0 x1 x2)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 x1).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) = y0) -> (y0 -> ((x1 x2) = (@ARB a1)) = y1) -> (((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) -> (x1 x2) = (@ARB a1)) = (y0 -> y1)) x3.
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @eq a1 (x0 x1).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, ((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 y0 x0))) -> (x1 y0) = (@ARB a1).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) := (forall y0 : a0, (~ (@IN a0 y0 x2)) -> (x0 y0) = (@ARB a1)) /\ (~ (@IN a0 x1 x2)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) := (((forall y0 : a0, (~ (@IN a0 y0 x2)) -> (x0 y0) = (@ARB a1)) /\ (~ (@IN a0 x1 x2))) -> ((x0 x1) = (@ARB a1)) = True) -> (((@IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 x2)) /\ (~ (@IN a0 x1 x2))) -> (x0 x1) = (@ARB a1)) = (((forall y0 : a0, (~ (@IN a0 y0 x2)) -> (x0 y0) = (@ARB a1)) /\ (~ (@IN a0 x1 x2))) -> True).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := ((forall y0 : a0, (~ (@IN a0 y0 x0)) -> (x1 y0) = (@ARB a1)) /\ (~ (@IN a0 x2 x0))) -> ((x1 x2) = (@ARB a1)) = True.
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : Prop) := (((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) = x3) -> (x3 -> ((x1 x2) = (@ARB a1)) = x4) -> (((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) -> (x1 x2) = (@ARB a1)) = (x3 -> x4).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> (@IN a0 x0 x1) = False.
Definition term29 (a0 : Type') := fun y0 : a0 => True.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, (@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 x0)) = (forall y1 : a0, (~ (@IN a0 y1 x0)) -> (y0 y1) = (@ARB a1)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@IN (a0 -> a1) y1 (@EXTENSIONAL a0 a1 y0)) = (forall y2 : a0, (~ (@IN a0 y2 y0)) -> (y1 y2) = (@ARB a1))) x0.
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (~ (@IN a0 y0 x0)) -> (x1 y0) = (@ARB a1)) x2.
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := fun y0 : a0 => ((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 y0 x0))) -> (x1 y0) = (@ARB a1).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := and (forall y0 : a0, (~ (@IN a0 y0 x0)) -> (x1 y0) = (@ARB a1)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) := forall y0 : Prop, (((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) = x3) -> (x3 -> ((x1 x2) = (@ARB a1)) = y0) -> (((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) -> (x1 x2) = (@ARB a1)) = (x3 -> y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (~ (@IN a0 x2 x0)) -> (x1 x2) = (@ARB a1).
Definition term34 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => True.
Definition term39 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, (((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) = y0) -> (y0 -> ((x1 x2) = (@ARB a1)) = y1) -> (((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) -> (x1 x2) = (@ARB a1)) = (y0 -> y1).
Definition term7 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) = x3) -> (x3 -> ((x1 x2) = (@ARB a1)) = y0) -> (((@IN (a0 -> a1) x1 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 x2 x0))) -> (x1 x2) = (@ARB a1)) = (x3 -> y0)) x4.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := and (@IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 x1)).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a1 => forall y1 : a0, ((@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 y1 x0))) -> (y0 y1) = (@ARB a1).
Definition term38 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : a0, ((@IN (a0 -> a1) y1 (@EXTENSIONAL a0 a1 y0)) /\ (~ (@IN a0 y2 y0))) -> (y1 y2) = (@ARB a1).
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) := ((forall y0 : a0, (~ (@IN a0 y0 x2)) -> (x0 y0) = (@ARB a1)) /\ (~ (@IN a0 x1 x2))) -> True.
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (((@IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 x2)) /\ (~ (@IN a0 x1 x2))) = ((forall y0 : a0, (~ (@IN a0 y0 x2)) -> (x0 y0) = (@ARB a1)) /\ (~ (@IN a0 x1 x2)))) -> (((forall y0 : a0, (~ (@IN a0 y0 x2)) -> (x0 y0) = (@ARB a1)) /\ (~ (@IN a0 x1 x2))) -> ((x0 x1) = (@ARB a1)) = x3) -> (((@IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 x2)) /\ (~ (@IN a0 x1 x2))) -> (x0 x1) = (@ARB a1)) = (((forall y0 : a0, (~ (@IN a0 y0 x2)) -> (x0 y0) = (@ARB a1)) /\ (~ (@IN a0 x1 x2))) -> x3).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : a0, ((@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 x0)) /\ (~ (@IN a0 y1 x0))) -> (y0 y1) = (@ARB a1).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 x0)) = (forall y1 : a0, (~ (@IN a0 y1 x0)) -> (y0 y1) = (@ARB a1))) x1.
Definition term41 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term36 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, True.
