Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => ((x1 x0) = (x1 y0)) /\ (x2 y0).
Definition term57 := (~ False) -> False.
Definition term44 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (~ ((x1 x0) = (x1 y0))) \/ (~ (x2 y0)).
Definition term33 (x0 : Prop) := ~ (~ x0).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term25 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3).
Definition term24 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 y1) -> @IN a1 (y0 y2) (@IMAGE a0 a1 y0 y1).
Definition term26 (x0 : Prop) := (~ x0) -> False.
Definition term56 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (((x0 x2) = (x0 x2)) /\ (x1 x2)) -> False.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x1) -> @IN a1 (x0 y0) (@IMAGE a0 a1 x0 x1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (x2 x0) -> exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := ((x1 x0) = (x1 x2)) /\ (@IN a0 x2 x3).
Definition term28 (a0 : Type') (a1 : Type') := ~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3)).
Definition term52 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term49 (x0 : Prop) := (~ x0) -> x0.
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (~ (exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0))) -> False.
Definition term53 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ((x1 x0) = (x1 x3)) /\ (x2 x3).
Definition term43 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ((x1 x0) = (x1 y1)) /\ (x2 y1)) y0).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := ~ (exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a1 x0 (@IMAGE a0 a1 x1 x2).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term29 (a0 : Type') (a1 : Type') := ((~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))) -> False.
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 y0) -> @IN a1 (x0 y1) (@IMAGE a0 a1 x0 y0).
Definition term45 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a0, (~ ((x1 x0) = (x1 y0))) \/ (~ (x2 y0)).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => ((x1 x0) = (x1 y0)) /\ (x2 y0)) x3.
Definition term37 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x1 x0) = (x1 x3))) \/ (~ (x2 x3)).
Definition term55 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) = (x0 x2)) /\ (x1 x2).
Definition term32 (a0 : Type') (a1 : Type') := ~ (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))).
Definition term27 (a0 : Type') (a1 : Type') := (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))) -> False.
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := forall y0 : a0, (x1 y0) -> exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1).
Definition term30 (a0 : Type') (a1 : Type') := (((~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))) -> False.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a1 (x1 x0) (@IMAGE a0 a1 x1 x2).
Definition term0 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (~ ((x0 x1) = (x0 x1))) -> (x0 x1) = (x0 x1).
Definition term54 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (((x1 x0) = (x1 x3)) /\ (x2 x3)) -> False.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (x2 y0).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (@IN a0 x0 x2) -> @IN a1 (x1 x0) (@IMAGE a0 a1 x1 x2).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ~ ((fun y0 : a0 => ((x1 x0) = (x1 y0)) /\ (x2 y0)) x3).
Definition term23 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3).
Definition term22 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 y1) -> @IN a1 (y0 y2) (@IMAGE a0 a1 y0 y1).
Definition term46 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (~ ((x1 x0) = (x1 y0))) \/ (~ (x2 y0))) x3.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) := and ((x1 x0) = (x1 x2)).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x1) -> @IN a1 (x0 y0) (@IMAGE a0 a1 x0 x1).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> Prop => forall y1 : a0, (y0 y1) -> exists y2 : a0, ((x0 y1) = (x0 y2)) /\ (y0 y2).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, ((x1 x0) = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term31 (a0 : Type') (a1 : Type') := (((~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))) -> False) -> ((~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, (y1 y2) -> exists y3 : a0, ((y0 y2) = (y0 y3)) /\ (y1 y3))) -> False.
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := fun y0 : a0 => (x1 y0) -> exists y1 : a0, ((x0 y0) = (x0 y1)) /\ (x1 y1).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => ((x1 x0) = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => ((x1 x0) = (x1 y1)) /\ (x2 y1)) y0).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, forall y1 : a0, (y0 y1) -> exists y2 : a0, ((x0 y1) = (x0 y2)) /\ (y0 y2).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 y0) -> @IN a1 (x0 y1) (@IMAGE a0 a1 x0 y0).
Definition term48 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := ~ ((x0 x1) = (x0 x1)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ~ (((x1 x0) = (x1 x3)) /\ (x2 x3)).
