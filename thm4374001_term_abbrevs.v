Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@UNIV a0) x1)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1) := forall y0 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 x0 x2) (@CROSS a1 a0 x1 y0)) = ((@IN a0 x0 x1) /\ (@IN a1 x2 y0)).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1 -> Prop) := @eq Prop ((@IN a0 x0 (@INTERS a0 (@EMPTY (a0 -> Prop)))) /\ (@IN a1 x1 x2)).
Definition term35 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) (x2 : a0) := forall y0 : a1, (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@UNIV a0) x1))) (@pair a0 a1 x2 y0).
Definition term22 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := forall y0 : a0, forall y1 : a1, (fun y2 : prod a0 a1 => (@IN (prod a0 a1) y2 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y2 (@CROSS a1 a0 (@UNIV a0) x1))) (@pair a0 a1 y0 y1).
Definition term19 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) := forall y0 : prod a0 a1, x0 y0.
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term46 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : type686 a0) (x3 : a1 -> Prop) := @eq Prop (@IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 (@INTERS a0 x2) x3)).
Definition term34 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a1 -> Prop) := fun y0 : a1 => (@IN (prod a0 a1) (@pair a0 a1 x1 y0) (@CROSS a1 a0 (@INTERS a0 x0) x2)) = (@IN (prod a0 a1) (@pair a0 a1 x1 y0) (@CROSS a1 a0 (@UNIV a0) x2)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, forall y2 : a0 -> Prop, forall y3 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@CROSS a1 a0 y2 y3)) = ((@IN a0 y0 y2) /\ (@IN a1 y1 y3))) x0.
Definition term25 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : type686 a0) (x2 : a1 -> Prop) := @IN (prod a0 a1) x0 (@CROSS a1 a0 (@INTERS a0 x1) x2).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1) (x3 : a1 -> Prop) := (@IN a0 x0 x1) /\ (@IN a1 x2 x3).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := fun y0 : prod a0 a1 => (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@UNIV a0) x1))) y0.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term49 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) := fun y0 : a1 => ((@IN a0 x0 (@INTERS a0 (@EMPTY (a0 -> Prop)))) /\ (@IN a1 y0 x1)) = ((@IN a0 x0 (@UNIV a0)) /\ (@IN a1 y0 x1)).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := @eq Prop (forall y0 : prod a0 a1, (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@UNIV a0) x1))) y0).
Definition term30 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) (x2 : a0) (x3 : a1) := (fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@UNIV a0) x1))) (@pair a0 a1 x2 x3).
Definition term51 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := fun y0 : a0 => forall y1 : a1, ((@IN a0 y0 (@INTERS a0 (@EMPTY (a0 -> Prop)))) /\ (@IN a1 y1 x0)) = ((@IN a0 y0 (@UNIV a0)) /\ (@IN a1 y1 x0)).
Definition term38 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := fun y0 : a0 => forall y1 : a1, (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@CROSS a1 a0 (@UNIV a0) x1)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 y0 y1)) = ((@IN a0 x0 y0) /\ (@IN a1 x1 y1))) x2.
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) (x1 : type1210 a0 a1) := forall y0 : prod a0 a1, (@IN (prod a0 a1) y0 x0) = (@IN (prod a0 a1) y0 x1).
Definition term17 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := @CROSS a1 a0 (@INTERS a0 x0) x1.
Definition term29 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := @eq Prop (forall y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@UNIV a0) x1))).
Definition term24 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) (x2 : prod a0 a1) := (fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@UNIV a0) x1))) x2.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term21 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := forall y0 : prod a0 a1, (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@UNIV a0) x1))) y0.
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) := forall y0 : a0, forall y1 : a1, x0 (@pair a0 a1 y0 y1).
Definition term41 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@INTERS a0 x1).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0 -> Prop) (x3 : a1 -> Prop) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 x2 x3).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1) (x3 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@IN (prod a0 a1) (@pair a0 a1 x0 x2) (@CROSS a1 a0 x1 y0)) = ((@IN a0 x0 x1) /\ (@IN a1 x2 y0))) x3.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 y0 y1)) = ((@IN a0 x0 y0) /\ (@IN a1 x1 y1)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@CROSS a1 a0 y1 y2)) = ((@IN a0 x0 y1) /\ (@IN a1 y0 y2)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := forall y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@UNIV a0) x1)).
Definition term42 (a0 : Type') (x0 : a0) := @IN a0 x0 (@INTERS a0 (@EMPTY (a0 -> Prop))).
Definition term45 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1 -> Prop) := (@IN a0 x0 (@INTERS a0 (@EMPTY (a0 -> Prop)))) /\ (@IN a1 x1 x2).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1 -> Prop) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 (@UNIV a0) x2).
Definition term52 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : a0, forall y1 : a1, ((@IN a0 y0 (@INTERS a0 (@EMPTY (a0 -> Prop)))) /\ (@IN a1 y1 x0)) = ((@IN a0 y0 (@UNIV a0)) /\ (@IN a1 y1 x0)).
Definition term39 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := forall y0 : a0, forall y1 : a1, (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@CROSS a1 a0 (@UNIV a0) x1)).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a1) (x3 : a1 -> Prop) := (@IN a0 x0 (@INTERS a0 x1)) /\ (@IN a1 x2 x3).
Definition term48 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1 -> Prop) := (@IN a0 x0 (@UNIV a0)) /\ (@IN a1 x1 x2).
Definition term33 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : a1 => (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@UNIV a0) x1))) (@pair a0 a1 x2 y0).
Definition term26 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a1 -> Prop) := @IN (prod a0 a1) x0 (@CROSS a1 a0 (@UNIV a0) x1).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : type686 a0) (x3 : a1 -> Prop) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 (@INTERS a0 x2) x3).
Definition term50 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) := forall y0 : a1, ((@IN a0 x0 (@INTERS a0 (@EMPTY (a0 -> Prop)))) /\ (@IN a1 y0 x1)) = ((@IN a0 x0 (@UNIV a0)) /\ (@IN a1 y0 x1)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a1 -> Prop) := forall y0 : a1, (@IN (prod a0 a1) (@pair a0 a1 x1 y0) (@CROSS a1 a0 (@INTERS a0 x0) x2)) = (@IN (prod a0 a1) (@pair a0 a1 x1 y0) (@CROSS a1 a0 (@UNIV a0) x2)).
Definition term44 (a0 : Type') (x0 : a0) := and (@IN a0 x0 (@INTERS a0 (@EMPTY (a0 -> Prop)))).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term43 (a0 : Type') (x0 : a0) (x1 : type686 a0) := and (@IN a0 x0 (@INTERS a0 x1)).
Definition term37 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1 -> Prop) := fun y0 : a0 => forall y1 : a1, (fun y2 : prod a0 a1 => (@IN (prod a0 a1) y2 (@CROSS a1 a0 (@INTERS a0 x0) x1)) = (@IN (prod a0 a1) y2 (@CROSS a1 a0 (@UNIV a0) x1))) (@pair a0 a1 y0 y1).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@CROSS a1 a0 y1 y2)) = ((@IN a0 x0 y1) /\ (@IN a1 y0 y2))) x1.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
