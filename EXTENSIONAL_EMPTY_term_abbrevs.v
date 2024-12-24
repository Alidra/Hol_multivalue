Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, (~ (@IN a0 y0 (@EMPTY a0))) -> (x0 y0) = (@ARB a1).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, (~ (@IN a0 y0 x0)) -> (x1 y0) = (@ARB a1).
Definition term43 (a0 : Type') (a1 : Type') := fun y0 : a0 => (fun y1 : a0 => @ARB a1) y0.
Definition term44 (a0 : Type') (a1 : Type') (x0 : a0) := @eq a1 ((fun y0 : a0 => (fun y1 : a0 => @ARB a1) y0) x0).
Definition term50 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => (x0 y0) = (@ARB a1).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0)) x1.
Definition term25 (a0 : Type') (x0 : a0) := imp (~ (@IN a0 x0 (@EMPTY a0))).
Definition term21 (a0 : Type') (a1 : Type') := @INSERT (a0 -> a1) (fun y0 : a0 => @ARB a1) (@EMPTY (a0 -> a1)).
Definition term51 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, x0.
Definition term37 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => (forall y1 : a0, (y0 y1) = (@ARB a1)) = (y0 = (fun y1 : a0 => @ARB a1)).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := @IN (a0 -> a1) x0 (@INSERT (a0 -> a1) x1 (@EMPTY (a0 -> a1))).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, (x0 y0) = (@ARB a1).
Definition term7 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@INSERT a0 y1 (@EMPTY a0))) = (y0 = y1)) x0.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 x1).
Definition term46 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @eq a1 (x0 x1).
Definition term36 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => (@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 (@EMPTY a0))) = (@IN (a0 -> a1) y0 (@INSERT (a0 -> a1) (fun y1 : a0 => @ARB a1) (@EMPTY (a0 -> a1)))).
Definition term45 (a0 : Type') (a1 : Type') (x0 : a0) := @eq a1 ((fun y0 : a0 => @ARB a1) x0).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := @IN (a0 -> a1) x0 (@INSERT (a0 -> a1) (fun y0 : a0 => @ARB a1) (@EMPTY (a0 -> a1))).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type572 a0 a1) (x1 : type572 a0 a1) := forall y0 : a0 -> a1, (@IN (a0 -> a1) y0 x0) = (@IN (a0 -> a1) y0 x1).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (~ (@IN a0 x1 (@EMPTY a0))) -> (x0 x1) = (@ARB a1).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => (x0 y0) = ((fun y1 : a0 => @ARB a1) y0).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => @ARB a1) x0.
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := @eq Prop (@IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 (@EMPTY a0))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, (@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 x0)) = (forall y1 : a0, (~ (@IN a0 y1 x0)) -> (y0 y1) = (@ARB a1)).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@IN (a0 -> a1) y1 (@EXTENSIONAL a0 a1 y0)) = (forall y2 : a0, (~ (@IN a0 y2 y0)) -> (y1 y2) = (@ARB a1))) x0.
Definition term48 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => True.
Definition term39 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, (x0 y0) = ((fun y1 : a0 => @ARB a1) y0).
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := True -> (x0 x1) = (@ARB a1).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => (~ (@IN a0 y0 (@EMPTY a0))) -> (x0 y0) = (@ARB a1).
Definition term8 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0).
Definition term38 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, (forall y1 : a0, (y0 y1) = (@ARB a1)) = (y0 = (fun y1 : a0 => @ARB a1)).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => (fun y1 : a0 => @ARB a1) y0) x0.
Definition term35 (a0 : Type') (a1 : Type') := fun y0 : a0 => @ARB a1.
Definition term6 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := @eq Prop (forall y0 : a0, (x0 y0) = (@ARB a1)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := @IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 (@EMPTY a0)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 x0)) = (forall y1 : a0, (~ (@IN a0 y1 x0)) -> (y0 y1) = (@ARB a1))) x1.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term4 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term49 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, True.
Definition term22 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, (@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 (@EMPTY a0))) = (@IN (a0 -> a1) y0 (@INSERT (a0 -> a1) (fun y1 : a0 => @ARB a1) (@EMPTY (a0 -> a1)))).
