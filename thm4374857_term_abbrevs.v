Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term54 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a1) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> (@IN a0 x1 y0) /\ (@IN a1 x2 (@UNIV a1)).
Definition term63 (a0 : Type') (a1 : Type') (x0 : type686 a0) := fun y0 : a0 => forall y1 : a1, ((@IN a0 y0 (@INTERS a0 x0)) /\ (@IN a1 y1 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) -> (@IN a0 y0 y2) /\ (@IN a1 y1 (@UNIV a1))).
Definition term19 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, ~ (x0 y0).
Definition term15 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop (x0 x1).
Definition term25 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term43 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term22 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : type686 a0) := (forall y0 : a1 -> Prop, ~ (x0 y0)) /\ (~ (forall y0 : a0 -> Prop, ~ (x1 y0))).
Definition term62 (a0 : Type') := forall y0 : a0, True.
Definition term32 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (x0 y0) -> y0 x1.
Definition term44 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @eq Prop (@IN (a0 -> Prop) x0 x1).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) := imp (@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))).
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN (a0 -> Prop) x1 (@EMPTY (a0 -> Prop))) -> @IN a0 x0 x1.
Definition term7 (a0 : Type') (x0 : type686 a0) := ~ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) = (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))).
Definition term13 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : type686 a0) := ((forall y0 : a1 -> Prop, (@IN (a1 -> Prop) y0 x0) = (@IN (a1 -> Prop) y0 (@EMPTY (a1 -> Prop)))) /\ (~ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) = (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))))) -> forall y0 : a0, forall y1 : a1, ((@IN a0 y0 (@INTERS a0 x1)) /\ (@IN a1 y1 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) -> (@IN a0 y0 y2) /\ (@IN a1 y1 (@UNIV a1))).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term31 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (x0 y0) -> y0 x1.
Definition term12 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : type686 a0) := ((x0 = (@EMPTY (a1 -> Prop))) /\ (~ (x1 = (@EMPTY (a0 -> Prop))))) -> forall y0 : a0, forall y1 : a1, ((@IN a0 y0 (@INTERS a0 x1)) /\ (@IN a1 y1 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) -> (@IN a0 y0 y2) /\ (@IN a1 y1 (@UNIV a1))).
Definition term27 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp (x0 x1).
Definition term59 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a1 => ((@IN a0 x1 (@INTERS a0 x0)) /\ (@IN a1 y0 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) -> (@IN a0 x1 y1) /\ (@IN a1 y0 (@UNIV a1))).
Definition term20 (a0 : Type') (x0 : type686 a0) := and (forall y0 : a0 -> Prop, ~ (x0 y0)).
Definition term3 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) = (@IN (a0 -> Prop) y0 x1).
Definition term58 (a0 : Type') (x0 : type686 a0) (x1 : a0) := @eq Prop (((forall y0 : a0 -> Prop, (x0 y0) -> y0 x1) = (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1)) = True).
Definition term46 (a0 : Type') (x0 : type686 a0) (x1 : a0) := (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1) /\ True.
Definition term40 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) -> @IN a0 x0 y0.
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term5 (a0 : Type') (x0 : type686 a0) := and (x0 = (@EMPTY (a0 -> Prop))).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : type686 a0) := (x0 = (@EMPTY (a1 -> Prop))) /\ (~ (x1 = (@EMPTY (a0 -> Prop)))).
Definition term51 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1) := (@IN a0 x0 x1) /\ (@IN a1 x2 (@UNIV a1)).
Definition term57 (a0 : Type') (x0 : type686 a0) (x1 : a0) := @eq Prop ((fun y0 : Prop => y0 = True) ((forall y0 : a0 -> Prop, (x0 y0) -> y0 x1) = (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1))).
Definition term60 (a0 : Type') := fun y0 : a0 => True.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term55 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a1) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> (@IN a0 x1 y0) /\ (@IN a1 x2 (@UNIV a1)).
Definition term0 (a0 : Type') (x0 : type686 a0) := ~ (x0 = (@EMPTY (a0 -> Prop))).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := imp (@IN (a0 -> Prop) x0 x1).
Definition term48 (a0 : Type') (x0 : type686 a0) (x1 : a0) := @eq Prop (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1).
Definition term24 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@INTERS a0 x1).
Definition term4 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) = (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))).
Definition term41 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term53 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : a1) := (@IN (a0 -> Prop) x2 x0) -> (@IN a0 x1 x2) /\ (@IN a1 x3 (@UNIV a1)).
Definition term17 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) = (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))).
Definition term9 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : type686 a0) := imp ((x0 = (@EMPTY (a1 -> Prop))) /\ (~ (x1 = (@EMPTY (a0 -> Prop))))).
Definition term64 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : type686 a0) := ((forall y0 : a1 -> Prop, ~ (x0 y0)) /\ (~ (forall y0 : a0 -> Prop, ~ (x1 y0)))) -> True.
Definition term35 (a0 : Type') (x0 : a0) := @IN a0 x0 (@INTERS a0 (@EMPTY (a0 -> Prop))).
Definition term6 (a0 : Type') (x0 : type686 a0) := and (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) = (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))).
Definition term23 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : type686 a0) := imp ((forall y0 : a1 -> Prop, ~ (x0 y0)) /\ (~ (forall y0 : a0 -> Prop, ~ (x1 y0)))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : type686 a0) := imp ((forall y0 : a1 -> Prop, (@IN (a1 -> Prop) y0 x0) = (@IN (a1 -> Prop) y0 (@EMPTY (a1 -> Prop)))) /\ (~ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) = (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))))).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type686 a0) := forall y0 : a0, forall y1 : a1, ((@IN a0 y0 (@INTERS a0 x0)) /\ (@IN a1 y1 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) -> (@IN a0 y0 y2) /\ (@IN a1 y1 (@UNIV a1))).
Definition term45 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a1) := (@IN a0 x0 (@INTERS a0 x1)) /\ (@IN a1 x2 (@INTERS a1 (@EMPTY (a1 -> Prop)))).
Definition term18 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => ~ (x0 y0).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := False -> x0 x1.
Definition term34 (a0 : Type') (x0 : type686 a0) (x1 : a0) := and (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a1) := @eq Prop ((@IN a0 x0 (@INTERS a0 x1)) /\ (@IN a1 x2 (@INTERS a1 (@EMPTY (a1 -> Prop))))).
Definition term56 (a0 : Type') (x0 : type686 a0) (x1 : a0) := (fun y0 : Prop => y0 = True) ((forall y0 : a0 -> Prop, (x0 y0) -> y0 x1) = (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1)).
Definition term16 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (x0 x1).
Definition term36 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) -> @IN a0 x0 y0.
Definition term61 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a1, ((@IN a0 x1 (@INTERS a0 x0)) /\ (@IN a1 y0 (@INTERS a1 (@EMPTY (a1 -> Prop))))) = (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) -> (@IN a0 x1 y1) /\ (@IN a1 y0 (@UNIV a1))).
Definition term33 (a0 : Type') (x0 : a0) (x1 : type686 a0) := and (@IN a0 x0 (@INTERS a0 x1)).
Definition term29 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 x1) -> x1 x2.
Definition term8 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : type686 a0) := (forall y0 : a1 -> Prop, (@IN (a1 -> Prop) y0 x0) = (@IN (a1 -> Prop) y0 (@EMPTY (a1 -> Prop)))) /\ (~ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) = (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))))).
Definition term21 (a0 : Type') (x0 : type686 a0) := ~ (forall y0 : a0 -> Prop, ~ (x0 y0)).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) /\ True.
Definition term28 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 x0) -> @IN a0 x1 x2.
Definition term42 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term30 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
