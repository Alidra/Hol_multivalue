Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : type24 a0 a1) := @eq Prop (x0 x1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : type56 a0 a1) := forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 x0) = (@IN ((cart a0 a1) -> Prop) y0 x1).
Definition term35 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : type24 a0 a1) (x2 : cart a0 a2) := (@IN (cart a0 a1) x0 x1) /\ (@IN (cart a0 a2) x2 (@UNIV (cart a0 a2))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := fun y0 : type24 a0 a1 => ~ (x0 y0).
Definition term42 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := (forall y0 : type24 a0 a1, ~ (x0 y0)) -> True.
Definition term18 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term29 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term14 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := imp (forall y0 : type24 a0 a1, ~ (x0 y0)).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : type24 a0 a1) := (forall y0 : type24 a0 a2, (@IN ((cart a0 a2) -> Prop) y0 x0) = (@IN ((cart a0 a2) -> Prop) y0 (@EMPTY ((cart a0 a2) -> Prop)))) -> forall y0 : cart a0 a1, forall y1 : cart a0 a2, ((@IN (cart a0 a1) y0 x1) /\ (@IN (cart a0 a2) y1 (@INTERS (cart a0 a2) (@EMPTY ((cart a0 a2) -> Prop))))) = ((@IN (cart a0 a1) y0 x1) /\ (@IN (cart a0 a2) y1 (@UNIV (cart a0 a2)))).
Definition term37 (a0 : Type') (a1 : Type') := fun y0 : cart a0 a1 => True.
Definition term20 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : cart a0 a1) := forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 x0) -> @IN (cart a0 a1) x1 y0.
Definition term32 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) (x1 : cart a0 a1) := (x0 x1) /\ True.
Definition term8 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) (x1 : type56 a0 a1) := @eq Prop (@IN ((cart a0 a1) -> Prop) x0 x1).
Definition term23 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) := imp (@IN ((cart a0 a1) -> Prop) x0 (@EMPTY ((cart a0 a1) -> Prop))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term41 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a1) := fun y0 : cart a0 a1 => forall y1 : cart a0 a2, ((@IN (cart a0 a1) y0 x0) /\ (@IN (cart a0 a2) y1 (@INTERS (cart a0 a2) (@EMPTY ((cart a0 a2) -> Prop))))) = ((@IN (cart a0 a1) y0 x0) /\ (@IN (cart a0 a2) y1 (@UNIV (cart a0 a2)))).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a1) := forall y0 : cart a0 a1, forall y1 : cart a0 a2, ((@IN (cart a0 a1) y0 x0) /\ (@IN (cart a0 a2) y1 (@INTERS (cart a0 a2) (@EMPTY ((cart a0 a2) -> Prop))))) = ((@IN (cart a0 a1) y0 x0) /\ (@IN (cart a0 a2) y1 (@UNIV (cart a0 a2)))).
Definition term19 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : type56 a0 a1) := @IN (cart a0 a1) x0 (@INTERS (cart a0 a1) x1).
Definition term33 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : type24 a0 a1) (x2 : cart a0 a2) := @eq Prop ((@IN (cart a0 a1) x0 x1) /\ (@IN (cart a0 a2) x2 (@INTERS (cart a0 a2) (@EMPTY ((cart a0 a2) -> Prop))))).
Definition term25 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) (x1 : cart a0 a1) := False -> x0 x1.
Definition term38 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : type24 a0 a1) := forall y0 : cart a0 a2, ((@IN (cart a0 a1) x0 x1) /\ (@IN (cart a0 a2) y0 (@INTERS (cart a0 a2) (@EMPTY ((cart a0 a2) -> Prop))))) = ((@IN (cart a0 a1) x0 x1) /\ (@IN (cart a0 a2) y0 (@UNIV (cart a0 a2)))).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 x0) = (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop))).
Definition term27 (a0 : Type') (a1 : Type') := fun y0 : type24 a0 a1 => True.
Definition term40 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : cart a0 a1, x0.
Definition term28 (a0 : Type') (a1 : Type') := forall y0 : type24 a0 a1, True.
Definition term11 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := fun y0 : type24 a0 a1 => (@IN ((cart a0 a1) -> Prop) y0 x0) = (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop))).
Definition term15 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : type24 a0 a1) := and (@IN (cart a0 a1) x0 x1).
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : type24 a0 a1) := (x0 = (@EMPTY ((cart a0 a2) -> Prop))) -> forall y0 : cart a0 a1, forall y1 : cart a0 a2, ((@IN (cart a0 a1) y0 x1) /\ (@IN (cart a0 a2) y1 (@INTERS (cart a0 a2) (@EMPTY ((cart a0 a2) -> Prop))))) = ((@IN (cart a0 a1) y0 x1) /\ (@IN (cart a0 a2) y1 (@UNIV (cart a0 a2)))).
Definition term39 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, True.
Definition term17 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@INTERS a0 x1).
Definition term34 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) (x1 : cart a0 a1) := @eq Prop (x0 x1).
Definition term36 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : type24 a0 a1) := fun y0 : cart a0 a2 => ((@IN (cart a0 a1) x0 x1) /\ (@IN (cart a0 a2) y0 (@INTERS (cart a0 a2) (@EMPTY ((cart a0 a2) -> Prop))))) = ((@IN (cart a0 a1) x0 x1) /\ (@IN (cart a0 a2) y0 (@UNIV (cart a0 a2)))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : type24 a0 a1) := ~ (x0 x1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := forall y0 : type24 a0 a1, ~ (x0 y0).
Definition term30 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : type24 a0 a1, x0.
Definition term31 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : type24 a0 a1) (x2 : cart a0 a2) := (@IN (cart a0 a1) x0 x1) /\ (@IN (cart a0 a2) x2 (@INTERS (cart a0 a2) (@EMPTY ((cart a0 a2) -> Prop)))).
Definition term24 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : type24 a0 a1) := (@IN ((cart a0 a1) -> Prop) x1 (@EMPTY ((cart a0 a1) -> Prop))) -> @IN (cart a0 a1) x0 x1.
Definition term22 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop))) -> @IN (cart a0 a1) x0 y0.
Definition term26 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := fun y0 : type24 a0 a1 => (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop))) -> @IN (cart a0 a1) x0 y0.
Definition term16 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) (x1 : cart a0 a1) := and (x0 x1).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := imp (forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 x0) = (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop)))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := imp (x0 = (@EMPTY ((cart a0 a1) -> Prop))).
Definition term21 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := @IN (cart a0 a1) x0 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop))).