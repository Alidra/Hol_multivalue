Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : cart a0 a1) := fun y0 : type24 a0 a1 => (@IN ((cart a0 a1) -> Prop) y0 x0) -> @IN (cart a0 a1) x1 y0.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : type24 a0 a1) := @eq Prop (x0 x1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : type56 a0 a1) := forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 x0) = (@IN ((cart a0 a1) -> Prop) y0 x1).
Definition term12 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := fun y0 : type24 a0 a1 => ~ (x0 y0).
Definition term53 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := (forall y0 : type24 a0 a1, ~ (x0 y0)) -> True.
Definition term16 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term27 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term14 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := imp (forall y0 : type24 a0 a1, ~ (x0 y0)).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a1) (x1 : type56 a0 a2) := (forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 x0) = (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop)))) -> forall y0 : cart a0 a1, forall y1 : cart a0 a2, ((@IN (cart a0 a1) y0 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop)))) /\ (@IN (cart a0 a2) y1 (@INTERS (cart a0 a2) x1))) = (forall y2 : type24 a0 a2, (@IN ((cart a0 a2) -> Prop) y2 x1) -> (@IN (cart a0 a1) y0 (@UNIV (cart a0 a1))) /\ (@IN (cart a0 a2) y1 y2)).
Definition term48 (a0 : Type') (a1 : Type') := fun y0 : cart a0 a1 => True.
Definition term44 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : cart a0 a1) (x2 : cart a0 a2) (x3 : type24 a0 a2) := (@IN ((cart a0 a2) -> Prop) x3 x0) -> (@IN (cart a0 a1) x1 (@UNIV (cart a0 a1))) /\ (@IN (cart a0 a2) x2 x3).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : cart a0 a1) := forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 x0) -> @IN (cart a0 a1) x1 y0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) (x1 : type56 a0 a1) := @eq Prop (@IN ((cart a0 a1) -> Prop) x0 x1).
Definition term21 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) := imp (@IN ((cart a0 a1) -> Prop) x0 (@EMPTY ((cart a0 a1) -> Prop))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term45 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : cart a0 a1) (x2 : cart a0 a2) := fun y0 : type24 a0 a2 => (@IN ((cart a0 a2) -> Prop) y0 x0) -> (@IN (cart a0 a1) x1 (@UNIV (cart a0 a1))) /\ (@IN (cart a0 a2) x2 y0).
Definition term41 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := and (@IN (cart a0 a1) x0 (@UNIV (cart a0 a1))).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) := forall y0 : cart a0 a1, forall y1 : cart a0 a2, ((@IN (cart a0 a1) y0 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop)))) /\ (@IN (cart a0 a2) y1 (@INTERS (cart a0 a2) x0))) = (forall y2 : type24 a0 a2, (@IN ((cart a0 a2) -> Prop) y2 x0) -> (@IN (cart a0 a1) y0 (@UNIV (cart a0 a1))) /\ (@IN (cart a0 a2) y1 y2)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : type56 a0 a1) := @IN (cart a0 a1) x0 (@INTERS (cart a0 a1) x1).
Definition term37 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) (x2 : type56 a0 a2) := (@IN (cart a0 a1) x0 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop)))) /\ (@IN (cart a0 a2) x1 (@INTERS (cart a0 a2) x2)).
Definition term23 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) (x1 : cart a0 a1) := False -> x0 x1.
Definition term49 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : cart a0 a1) := forall y0 : cart a0 a2, ((@IN (cart a0 a1) x1 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop)))) /\ (@IN (cart a0 a2) y0 (@INTERS (cart a0 a2) x0))) = (forall y1 : type24 a0 a2, (@IN ((cart a0 a2) -> Prop) y1 x0) -> (@IN (cart a0 a1) x1 (@UNIV (cart a0 a1))) /\ (@IN (cart a0 a2) y0 y1)).
Definition term52 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) := fun y0 : cart a0 a1 => forall y1 : cart a0 a2, ((@IN (cart a0 a1) y0 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop)))) /\ (@IN (cart a0 a2) y1 (@INTERS (cart a0 a2) x0))) = (forall y2 : type24 a0 a2, (@IN ((cart a0 a2) -> Prop) y2 x0) -> (@IN (cart a0 a1) y0 (@UNIV (cart a0 a1))) /\ (@IN (cart a0 a2) y1 y2)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 x0) = (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop))).
Definition term25 (a0 : Type') (a1 : Type') := fun y0 : type24 a0 a1 => True.
Definition term38 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : cart a0 a1) := True /\ (forall y0 : type24 a0 a1, (x0 y0) -> y0 x1).
Definition term39 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) (x2 : type56 a0 a2) := @eq Prop ((@IN (cart a0 a1) x0 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop)))) /\ (@IN (cart a0 a2) x1 (@INTERS (cart a0 a2) x2))).
Definition term51 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : cart a0 a1, x0.
Definition term36 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : cart a0 a1) := forall y0 : type24 a0 a1, (x0 y0) -> y0 x1.
Definition term26 (a0 : Type') (a1 : Type') := forall y0 : type24 a0 a1, True.
Definition term47 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : cart a0 a1) := fun y0 : cart a0 a2 => ((@IN (cart a0 a1) x1 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop)))) /\ (@IN (cart a0 a2) y0 (@INTERS (cart a0 a2) x0))) = (forall y1 : type24 a0 a2, (@IN ((cart a0 a2) -> Prop) y1 x0) -> (@IN (cart a0 a1) x1 (@UNIV (cart a0 a1))) /\ (@IN (cart a0 a2) y0 y1)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := fun y0 : type24 a0 a1 => (@IN ((cart a0 a1) -> Prop) y0 x0) = (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop))).
Definition term43 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) (x1 : cart a0 a1) := True /\ (x0 x1).
Definition term35 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : cart a0 a1) := fun y0 : type24 a0 a1 => (x0 y0) -> y0 x1.
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a1) (x1 : type56 a0 a2) := (x0 = (@EMPTY ((cart a0 a1) -> Prop))) -> forall y0 : cart a0 a1, forall y1 : cart a0 a2, ((@IN (cart a0 a1) y0 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop)))) /\ (@IN (cart a0 a2) y1 (@INTERS (cart a0 a2) x1))) = (forall y2 : type24 a0 a2, (@IN ((cart a0 a2) -> Prop) y2 x1) -> (@IN (cart a0 a1) y0 (@UNIV (cart a0 a1))) /\ (@IN (cart a0 a2) y1 y2)).
Definition term50 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, True.
Definition term30 (a0 : Type') (a1 : Type') (x0 : type24 a0 a1) (x1 : type56 a0 a1) := imp (@IN ((cart a0 a1) -> Prop) x0 x1).
Definition term40 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : cart a0 a1) := @eq Prop (forall y0 : type24 a0 a1, (x0 y0) -> y0 x1).
Definition term31 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : type24 a0 a1) := imp (x0 x1).
Definition term15 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@INTERS a0 x1).
Definition term29 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := and (@IN (cart a0 a1) x0 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop)))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : type24 a0 a1) := ~ (x0 x1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := forall y0 : type24 a0 a1, ~ (x0 y0).
Definition term28 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : type24 a0 a1, x0.
Definition term22 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : type24 a0 a1) := (@IN ((cart a0 a1) -> Prop) x1 (@EMPTY ((cart a0 a1) -> Prop))) -> @IN (cart a0 a1) x0 x1.
Definition term20 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop))) -> @IN (cart a0 a1) x0 y0.
Definition term24 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := fun y0 : type24 a0 a1 => (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop))) -> @IN (cart a0 a1) x0 y0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := imp (forall y0 : type24 a0 a1, (@IN ((cart a0 a1) -> Prop) y0 x0) = (@IN ((cart a0 a1) -> Prop) y0 (@EMPTY ((cart a0 a1) -> Prop)))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := imp (x0 = (@EMPTY ((cart a0 a1) -> Prop))).
Definition term42 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) (x2 : type24 a0 a2) := (@IN (cart a0 a1) x0 (@UNIV (cart a0 a1))) /\ (@IN (cart a0 a2) x1 x2).
Definition term46 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : cart a0 a1) (x2 : cart a0 a2) := forall y0 : type24 a0 a2, (@IN ((cart a0 a2) -> Prop) y0 x0) -> (@IN (cart a0 a1) x1 (@UNIV (cart a0 a1))) /\ (@IN (cart a0 a2) x2 y0).
Definition term32 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : cart a0 a1) (x2 : type24 a0 a1) := (@IN ((cart a0 a1) -> Prop) x2 x0) -> @IN (cart a0 a1) x1 x2.
Definition term33 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) (x1 : type24 a0 a1) (x2 : cart a0 a1) := (x0 x1) -> x1 x2.
Definition term19 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := @IN (cart a0 a1) x0 (@INTERS (cart a0 a1) (@EMPTY ((cart a0 a1) -> Prop))).
