Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, ~ (x0 y0).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a1, ((@IN a0 y0 x0) /\ (@IN a1 y1 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = ((@IN a0 y0 x0) /\ (@IN a1 y1 (@UNIV a1))).
Definition term9 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop (x0 x1).
Definition term39 (a0 : Type') (x0 : type686 a0) := (forall y0 : a0 -> Prop, ~ (x0 y0)) -> True.
Definition term18 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term27 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term14 (a0 : Type') (x0 : type686 a0) := imp (forall y0 : a0 -> Prop, ~ (x0 y0)).
Definition term37 (a0 : Type') := forall y0 : a0, True.
Definition term7 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> Prop) := (forall y0 : a1 -> Prop, (@IN (a1 -> Prop) y0 x0) = (@IN (a1 -> Prop) y0 (@EMPTY (a1 -> Prop)))) -> forall y0 : a0, forall y1 : a1, ((@IN a0 y0 x1) /\ (@IN a1 y1 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = ((@IN a0 y0 x1) /\ (@IN a1 y1 (@UNIV a1))).
Definition term28 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @eq Prop (@IN (a0 -> Prop) x0 x1).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := imp (@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN (a0 -> Prop) x1 (@EMPTY (a0 -> Prop))) -> @IN a0 x0 x1.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1) := (@IN a0 x0 x1) /\ (@IN a1 x2 (@INTERS a1 (@EMPTY (a1 -> Prop)))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a1, ((@IN a0 x0 x1) /\ (@IN a1 y0 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = ((@IN a0 x0 x1) /\ (@IN a1 y0 (@UNIV a1))).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1) := @eq Prop ((@IN a0 x0 x1) /\ (@IN a1 x2 (@INTERS a1 (@EMPTY (a1 -> Prop))))).
Definition term1 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) = (@IN (a0 -> Prop) y0 x1).
Definition term24 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) -> @IN a0 x0 y0.
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1) := (@IN a0 x0 x1) /\ (@IN a1 x2 (@UNIV a1)).
Definition term35 (a0 : Type') := fun y0 : a0 => True.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term17 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@INTERS a0 x1).
Definition term2 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) = (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))).
Definition term25 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a1 => ((@IN a0 x0 x1) /\ (@IN a1 y0 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = ((@IN a0 x0 x1) /\ (@IN a1 y0 (@UNIV a1))).
Definition term11 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) = (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))).
Definition term19 (a0 : Type') (x0 : a0) := @IN a0 x0 (@INTERS a0 (@EMPTY (a0 -> Prop))).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> Prop) := (x0 = (@EMPTY (a1 -> Prop))) -> forall y0 : a0, forall y1 : a1, ((@IN a0 y0 x1) /\ (@IN a1 y1 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = ((@IN a0 y0 x1) /\ (@IN a1 y1 (@UNIV a1))).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a1, ((@IN a0 y0 x0) /\ (@IN a1 y1 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = ((@IN a0 y0 x0) /\ (@IN a1 y1 (@UNIV a1))).
Definition term12 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => ~ (x0 y0).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := False -> x0 x1.
Definition term4 (a0 : Type') (x0 : type686 a0) := imp (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) = (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))).
Definition term3 (a0 : Type') (x0 : type686 a0) := imp (x0 = (@EMPTY (a0 -> Prop))).
Definition term10 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (x0 x1).
Definition term20 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) -> @IN a0 x0 y0.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) /\ True.
Definition term26 (a0 : Type') := forall y0 : a0 -> Prop, True.
