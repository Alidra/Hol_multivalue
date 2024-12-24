Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term48 (x0 : Prop) := ~ (~ x0).
Definition term26 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term53 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term38 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) (@INTERS a0 x1))).
Definition term43 (a0 : Type') (x0 : a0) (x1 : type686 a0) := ~ (@IN a0 x0 (@INTERS a0 x1)).
Definition term52 (a0 : Type') := forall y0 : a0, True.
Definition term19 (a0 : Type') := forall y0 : type686 a0, (@INTERS a0 y0) = (@DIFF a0 (@UNIV a0) (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@IN (a0 -> Prop) y2 y0) (@DIFF a0 (@UNIV a0) y2))))).
Definition term33 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (x0 y0) -> y0 x1.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term32 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (x0 y0) -> y0 x1.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : type686 a0 => (@DIFF a0 x0 (@INTERS a0 y0)) = (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@IN (a0 -> Prop) y2 y0) (@DIFF a0 x0 y2)))).
Definition term12 (a0 : Type') (x0 : type686 a0) := @UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@IN (a0 -> Prop) y1 x0) (@DIFF a0 (@UNIV a0) y1))).
Definition term1 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@IN (a0 -> Prop) y1 x0) (@DIFF a0 x1 y1))).
Definition term28 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp (x0 x1).
Definition term20 (a0 : Type') := forall y0 : type686 a0, (@INTERS a0 y0) = (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) (@INTERS a0 y0))).
Definition term7 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : type686 a0, (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@IN (a0 -> Prop) y3 y1) (@DIFF a0 y0 y3)))) = (@DIFF a0 y0 (@INTERS a0 y1)).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@DIFF a0 x1 x2).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @DIFF a0 x0 (@INTERS a0 x1).
Definition term24 (a0 : Type') := forall y0 : type686 a0, forall y1 : a0, (@IN a0 y1 (@INTERS a0 y0)) = (@IN a0 y1 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) (@INTERS a0 y0)))).
Definition term41 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@DIFF a0 (@UNIV a0) (@INTERS a0 x1)).
Definition term17 (a0 : Type') := fun y0 : type686 a0 => (@INTERS a0 y0) = (@DIFF a0 (@UNIV a0) (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@IN (a0 -> Prop) y2 y0) (@DIFF a0 (@UNIV a0) y2))))).
Definition term45 (a0 : Type') (x0 : type686 a0) (x1 : a0) := True /\ (~ (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1)).
Definition term49 (a0 : Type') (x0 : type686 a0) (x1 : a0) := True /\ (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : type686 a0 => (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@IN (a0 -> Prop) y2 y0) (@DIFF a0 x0 y2)))) = (@DIFF a0 x0 (@INTERS a0 y0)).
Definition term23 (a0 : Type') := fun y0 : type686 a0 => forall y1 : a0, (@IN a0 y1 (@INTERS a0 y0)) = (@IN a0 y1 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) (@INTERS a0 y0)))).
Definition term55 (a0 : Type') := forall y0 : type686 a0, True.
Definition term51 (a0 : Type') := fun y0 : a0 => True.
Definition term15 (a0 : Type') (x0 : type686 a0) := @DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) (@INTERS a0 x0)).
Definition term13 (a0 : Type') (x0 : type686 a0) := @DIFF a0 (@UNIV a0) (@INTERS a0 x0).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : type686 a0, (@DIFF a0 x0 (@INTERS a0 y0)) = (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@IN (a0 -> Prop) y2 y0) (@DIFF a0 x0 y2)))).
Definition term42 (a0 : Type') (x0 : a0) (x1 : type686 a0) := (@IN a0 x0 (@UNIV a0)) /\ (~ (@IN a0 x0 (@INTERS a0 x1))).
Definition term22 (a0 : Type') (x0 : type686 a0) := forall y0 : a0, (@IN a0 y0 (@INTERS a0 x0)) = (@IN a0 y0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) (@INTERS a0 x0)))).
Definition term54 (a0 : Type') := fun y0 : type686 a0 => True.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := imp (@IN (a0 -> Prop) x0 x1).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : type686 a0, (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@IN (a0 -> Prop) y3 y1) (@DIFF a0 y0 y3)))) = (@DIFF a0 y0 (@INTERS a0 y1))) x0.
Definition term35 (a0 : Type') (x0 : type686 a0) (x1 : a0) := @eq Prop (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1).
Definition term25 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@INTERS a0 x1).
Definition term47 (a0 : Type') (x0 : type686 a0) (x1 : a0) := ~ (~ (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1)).
Definition term34 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @eq Prop (@IN a0 x0 (@INTERS a0 x1)).
Definition term9 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : type686 a0, (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@IN (a0 -> Prop) y3 y1) (@DIFF a0 y0 y3)))) = (@DIFF a0 y0 (@INTERS a0 y1)).
Definition term8 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : type686 a0, (@DIFF a0 y0 (@INTERS a0 y1)) = (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@IN (a0 -> Prop) y3 y1) (@DIFF a0 y0 y3)))).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : type686 a0, (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@IN (a0 -> Prop) y2 y0) (@DIFF a0 x0 y2)))) = (@DIFF a0 x0 (@INTERS a0 y0)).
Definition term39 (a0 : Type') (x0 : a0) (x1 : type686 a0) := (@IN a0 x0 (@UNIV a0)) /\ (~ (@IN a0 x0 (@DIFF a0 (@UNIV a0) (@INTERS a0 x1)))).
Definition term50 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 => (@IN a0 y0 (@INTERS a0 x0)) = (@IN a0 y0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) (@INTERS a0 x0)))).
Definition term56 (a0 : Type') (x0 : Prop) := forall y0 : type686 a0, x0.
Definition term46 (a0 : Type') (x0 : a0) (x1 : type686 a0) := ~ (@IN a0 x0 (@DIFF a0 (@UNIV a0) (@INTERS a0 x1))).
Definition term16 (a0 : Type') (x0 : type686 a0) := @eq (a0 -> Prop) (@INTERS a0 x0).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := (fun y0 : type686 a0 => (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@IN (a0 -> Prop) y2 y0) (@DIFF a0 x0 y2)))) = (@DIFF a0 x0 (@INTERS a0 y0))) x1.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (~ (@IN a0 x1 x2)).
Definition term6 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : type686 a0, (@DIFF a0 y0 (@INTERS a0 y1)) = (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@IN (a0 -> Prop) y3 y1) (@DIFF a0 y0 y3)))).
Definition term40 (a0 : Type') (x0 : a0) := and (@IN a0 x0 (@UNIV a0)).
Definition term18 (a0 : Type') := fun y0 : type686 a0 => (@INTERS a0 y0) = (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) (@INTERS a0 y0))).
Definition term14 (a0 : Type') (x0 : type686 a0) := @DIFF a0 (@UNIV a0) (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@IN (a0 -> Prop) y1 x0) (@DIFF a0 (@UNIV a0) y1)))).
Definition term30 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 x1) -> x1 x2.
Definition term44 (a0 : Type') (x0 : type686 a0) (x1 : a0) := ~ (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1).
Definition term29 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 x0) -> @IN a0 x1 x2.
Definition term31 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
