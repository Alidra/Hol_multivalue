Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term91 := (~ False) -> False.
Definition term69 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : a1) := @eq Prop ((fun y0 : a1 => (~ (y0 = (x0 x1))) \/ (~ (@IN a0 x1 x2))) x3).
Definition term43 (x0 : Prop) := ~ (~ x0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) := forall y0 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y0 x1)) = (exists y1 : a0, (x0 = (y0 y1)) /\ (@IN a0 y1 x1)).
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y0) -> @IN a0 y2 y1) -> forall y2 : a1, (exists y3 : a0, (y2 = (x0 y3)) /\ (@IN a0 y3 y0)) -> exists y3 : a0, (y2 = (x0 y3)) /\ (@IN a0 y3 y1).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a1, (@IN a1 y0 (@IMAGE a0 a1 x1 x0)) -> @IN a1 y0 (@IMAGE a0 a1 x1 x2).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (~ (@IN a0 x1 x2)).
Definition term67 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (fun y0 : a1 => (~ (y0 = (x2 x0))) \/ (~ (@IN a0 x0 x1))) (x2 x3).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (~ (@IN a0 x1 x0)) \/ (@IN a0 x1 x2).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term35 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2).
Definition term34 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (@SUBSET a0 y1 y2) -> @SUBSET a1 (@IMAGE a0 a1 y0 y1) (@IMAGE a0 a1 y0 y2).
Definition term36 (x0 : Prop) := (~ x0) -> False.
Definition term70 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := @eq Prop ((~ (x0 = (x1 x2))) \/ (~ (@IN a0 x2 x3))).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ (@IN a0 y0 x1).
Definition term79 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (@IN a1 y0 (@IMAGE a0 a1 y2 y1)) = (exists y3 : a0, (y0 = (y2 y3)) /\ (@IN a0 y3 y1))) x0.
Definition term88 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := ((x1 x0) = (x1 x2)) /\ (@IN a0 x2 x3).
Definition term75 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (@SUBSET a0 x0 x1).
Definition term38 (a0 : Type') (a1 : Type') := ~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2)).
Definition term84 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term73 (x0 : Prop) := (~ x0) -> x0.
Definition term68 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := (~ ((x1 x0) = (x1 x2))) \/ (~ (@IN a0 x2 x3)).
Definition term89 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) := ((x0 x1) = (x0 x1)) /\ (@IN a0 x1 x2).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) -> @SUBSET a1 (@IMAGE a0 a1 x0 y0) (@IMAGE a0 a1 x0 y1).
Definition term48 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (~ (exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 x2))) -> False.
Definition term85 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a1 => (exists y1 : a0, (y0 = (x1 y1)) /\ (@IN a0 y1 x0)) -> exists y1 : a0, (y0 = (x1 y1)) /\ (@IN a0 y1 x2).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y1 y0)) = (exists y2 : a0, (x0 = (y1 y2)) /\ (@IN a0 y2 y0))) x1.
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @SUBSET a1 (@IMAGE a0 a1 x1 x0) (@IMAGE a0 a1 x1 x2).
Definition term60 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (x0 = (x1 y1)) /\ (@IN a0 y1 x2)) y0).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x2) -> forall y0 : a1, (exists y1 : a0, (y0 = (x1 y1)) /\ (@IN a0 y1 x0)) -> exists y1 : a0, (y0 = (x1 y1)) /\ (@IN a0 y1 x2).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a1 x0 (@IMAGE a0 a1 x1 x2).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := imp (@IN a1 x0 (@IMAGE a0 a1 x1 x2)).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) -> @SUBSET a1 (@IMAGE a0 a1 x1 x0) (@IMAGE a0 a1 x1 y0).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term39 (a0 : Type') (a1 : Type') := ((~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))) -> False.
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0) -> forall y1 : a1, (exists y2 : a0, (y1 = (x1 y2)) /\ (@IN a0 y2 x0)) -> exists y2 : a0, (y1 = (x1 y2)) /\ (@IN a0 y2 y0).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ (@IN a0 y0 x1)) x2.
Definition term66 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : a1) := (fun y0 : a1 => (~ (y0 = (x0 x1))) \/ (~ (@IN a0 x1 x2))) x3.
Definition term65 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) := fun y0 : a1 => (~ (y0 = (x0 x1))) \/ (~ (@IN a0 x1 x2)).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term49 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := ~ (exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 x2)).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, (@SUBSET a0 x0 y0) -> @SUBSET a1 (@IMAGE a0 a1 x1 x0) (@IMAGE a0 a1 x1 y0).
Definition term61 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (~ (x0 = (x1 y0))) \/ (~ (@IN a0 y0 x2)).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := imp (exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 x2)).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) = (forall y2 : a0, (@IN a0 y2 y0) -> @IN a0 y2 y1)) x0.
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (~ (@IN a0 x0 x1)).
Definition term42 (a0 : Type') (a1 : Type') := ~ (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))).
Definition term37 (a0 : Type') (a1 : Type') := (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))) -> False.
Definition term74 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> @IN a0 x0 x1.
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := (@IN a1 x1 (@IMAGE a0 a1 x2 x0)) -> @IN a1 x1 (@IMAGE a0 a1 x2 x3).
Definition term59 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ~ ((fun y0 : a0 => (x0 = (x1 y0)) /\ (@IN a0 y0 x2)) x3).
Definition term90 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0 -> Prop) := (((x0 x1) = (x0 x1)) /\ (@IN a0 x1 x2)) -> False.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (@SUBSET a0 x0 x2) -> @SUBSET a1 (@IMAGE a0 a1 x1 x0) (@IMAGE a0 a1 x1 x2).
Definition term40 (a0 : Type') (a1 : Type') := (((~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))) -> False.
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a1 => (@IN a1 y0 (@IMAGE a0 a1 x1 x0)) -> @IN a1 y0 (@IMAGE a0 a1 x1 x2).
Definition term83 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term62 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a0, (~ (x0 = (x1 y0))) \/ (~ (@IN a0 y0 x2)).
Definition term71 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (~ ((x0 x1) = (x0 x1))) -> (x0 x1) = (x0 x1).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y0) -> @IN a0 y2 y1) -> forall y2 : a1, (exists y3 : a0, (y2 = (x0 y3)) /\ (@IN a0 y3 y0)) -> exists y3 : a0, (y2 = (x0 y3)) /\ (@IN a0 y3 y1).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) -> @SUBSET a1 (@IMAGE a0 a1 x0 y0) (@IMAGE a0 a1 x0 y1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y1 y0)) = (exists y2 : a0, (x0 = (y1 y2)) /\ (@IN a0 y2 y0)).
Definition term53 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := ~ ((x0 = (x1 x2)) /\ (@IN a0 x2 x3)).
Definition term58 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (x0 = (x1 y0)) /\ (@IN a0 y0 x2)) x3.
Definition term45 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (x0 = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a1, (exists y1 : a0, (y0 = (x1 y1)) /\ (@IN a0 y1 x0)) -> exists y1 : a0, (y0 = (x1 y1)) /\ (@IN a0 y1 x2).
Definition term86 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := ~ (((x1 x0) = (x1 x2)) /\ (@IN a0 x2 x3)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) (x2 : a0 -> a1) := (fun y0 : a0 -> a1 => (@IN a1 x0 (@IMAGE a0 a1 y0 x1)) = (exists y1 : a0, (x0 = (y0 y1)) /\ (@IN a0 y1 x1))) x2.
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0) -> forall y1 : a1, (exists y2 : a0, (y1 = (x1 y2)) /\ (@IN a0 y2 x0)) -> exists y2 : a0, (y1 = (x1 y2)) /\ (@IN a0 y2 y0).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := @eq Prop ((~ (@IN a0 x1 x0)) \/ (@IN a0 x1 x2)).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := @eq Prop ((@IN a0 x1 x0) \/ (~ (@IN a0 x1 x2))).
Definition term33 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2).
Definition term32 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (@SUBSET a0 y1 y2) -> @SUBSET a1 (@IMAGE a0 a1 y0 y1) (@IMAGE a0 a1 y0 y2).
Definition term54 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := (~ (x0 = (x1 x2))) \/ (~ (@IN a0 x2 x3)).
Definition term64 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (~ (x0 = (x1 y0))) \/ (~ (@IN a0 y0 x2))) x3.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term44 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := (x0 = (x1 x2)) /\ (@IN a0 x2 x3).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term41 (a0 : Type') (a1 : Type') := (((~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))) -> False) -> ((~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y1) -> @IN a0 y3 y2) -> forall y3 : a1, (exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y1)) -> exists y4 : a0, (y3 = (y0 y4)) /\ (@IN a0 y4 y2))) -> False.
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (~ (~ (@IN a0 x1 x0))) -> @IN a0 x1 x2.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (@IN a0 y0 x1).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) -> @IN a0 x1 x2.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0)) x1.
Definition term57 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => (x0 = (x1 y1)) /\ (@IN a0 y1 x2)) y0).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := (exists y0 : a0, (x1 = (x2 y0)) /\ (@IN a0 y0 x0)) -> exists y0 : a0, (x1 = (x2 y0)) /\ (@IN a0 y0 x3).
Definition term72 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := ~ ((x0 x1) = (x0 x1)).
Definition term87 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := (((x1 x0) = (x1 x2)) /\ (@IN a0 x2 x3)) -> False.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0).
Definition term82 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (~ (~ (@IN a0 x0 x1))).
