Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> @IN (a0 -> Prop) y0 x1.
Definition term31 (a0 : Type') (x0 : a0) (x1 : type686 a0) := imp (@IN a0 x0 (@INTERS a0 x1)).
Definition term18 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : type686 a0) := (@IN (a0 -> Prop) x1 x0) -> @IN (a0 -> Prop) x1 x2.
Definition term55 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (x1 y0).
Definition term90 := (~ False) -> False.
Definition term53 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (~ (x0 x2)) \/ (x1 x2).
Definition term82 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (@I ((a0 -> Prop) -> Prop) x0 x2) -> @I ((a0 -> Prop) -> Prop) x1 x2.
Definition term50 (x0 : Prop) := ~ (~ x0).
Definition term12 (a0 : Type') := fun y0 : type686 a0 => forall y1 : type686 a0, (@SUBSET (a0 -> Prop) y1 y0) -> @SUBSET a0 (@INTERS a0 y0) (@INTERS a0 y1).
Definition term62 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (~ (@I ((a0 -> Prop) -> Prop) x0 x1)).
Definition term41 (a0 : Type') := fun y0 : type686 a0 => forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2.
Definition term13 (a0 : Type') := fun y0 : type686 a0 => forall y1 : type686 a0, (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> @IN (a0 -> Prop) y2 y0) -> forall y2 : a0, (@IN a0 y2 (@INTERS a0 y0)) -> @IN a0 y2 (@INTERS a0 y1).
Definition term8 (a0 : Type') (x0 : type686 a0) := fun y0 : type686 a0 => (@SUBSET (a0 -> Prop) y0 x0) -> @SUBSET a0 (@INTERS a0 x0) (@INTERS a0 y0).
Definition term76 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := @eq Prop ((@I ((a0 -> Prop) -> Prop) x0 x2) \/ (~ (@I ((a0 -> Prop) -> Prop) x1 x2))).
Definition term70 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (@I ((a0 -> Prop) -> Prop) x1 y0)) x2.
Definition term25 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term66 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (@I (a0 -> Prop) x1 x2).
Definition term43 (x0 : Prop) := (~ x0) -> False.
Definition term68 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (@I (a0 -> Prop) y0 x1).
Definition term36 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := fun y0 : a0 => (forall y1 : a0 -> Prop, (x0 y1) -> y1 y0) -> forall y1 : a0 -> Prop, (x1 y1) -> y1 y0.
Definition term85 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := @eq Prop ((@I (a0 -> Prop) x2 x0) \/ (~ (@I ((a0 -> Prop) -> Prop) x1 x2))).
Definition term1 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN (a0 -> Prop) y0 x1.
Definition term71 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (@I (a0 -> Prop) y0 x1)) x2.
Definition term30 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (x0 y0) -> y0 x1.
Definition term77 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term87 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (@I ((a0 -> Prop) -> Prop) x0 x1) -> @I (a0 -> Prop) x1 x2.
Definition term7 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) -> @IN (a0 -> Prop) y0 x0) -> forall y0 : a0, (@IN a0 y0 (@INTERS a0 x0)) -> @IN a0 y0 (@INTERS a0 x1).
Definition term6 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (@SUBSET (a0 -> Prop) x1 x0) -> @SUBSET a0 (@INTERS a0 x0) (@INTERS a0 x1).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (@I (a0 -> Prop) x0 x1)) -> @I (a0 -> Prop) x0 x1.
Definition term2 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := imp (@SUBSET (a0 -> Prop) x0 x1).
Definition term29 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (x0 y0) -> y0 x1.
Definition term45 (a0 : Type') := ~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2).
Definition term73 (x0 : Prop) := (~ x0) -> x0.
Definition term33 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : type686 a0) := (@IN a0 x1 (@INTERS a0 x0)) -> @IN a0 x1 (@INTERS a0 x2).
Definition term17 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp (x0 x1).
Definition term57 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (~ (x0 y0)) \/ (y0 x1).
Definition term75 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := @eq Prop ((~ (@I ((a0 -> Prop) -> Prop) x0 x2)) \/ (@I ((a0 -> Prop) -> Prop) x1 x2)).
Definition term35 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := fun y0 : a0 => (@IN a0 y0 (@INTERS a0 x0)) -> @IN a0 y0 (@INTERS a0 x1).
Definition term86 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (@I ((a0 -> Prop) -> Prop) x0 x1))) -> @I (a0 -> Prop) x1 x2.
Definition term79 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (~ (@I ((a0 -> Prop) -> Prop) x0 x1)).
Definition term56 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x1)) \/ (x1 x2).
Definition term63 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (~ (@I ((a0 -> Prop) -> Prop) x0 x2)) \/ (@I ((a0 -> Prop) -> Prop) x1 x2).
Definition term72 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) -> @I ((a0 -> Prop) -> Prop) x0 x1.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> False.
Definition term46 (a0 : Type') := ((~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)) -> False) -> (~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)) -> False.
Definition term61 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (~ (x0 x1)).
Definition term37 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0, (forall y1 : a0 -> Prop, (x0 y1) -> y1 y0) -> forall y1 : a0 -> Prop, (x1 y1) -> y1 y0.
Definition term78 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (~ (~ (@I ((a0 -> Prop) -> Prop) x0 x2))) -> @I ((a0 -> Prop) -> Prop) x1 x2.
Definition term65 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (@I ((a0 -> Prop) -> Prop) x1 y0).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := imp (@IN (a0 -> Prop) x0 x1).
Definition term24 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@INTERS a0 x1).
Definition term49 (a0 : Type') := ~ (~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)).
Definition term44 (a0 : Type') := (~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)) -> False.
Definition term21 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := fun y0 : a0 -> Prop => (x0 y0) -> x1 y0.
Definition term47 (a0 : Type') := (((~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)) -> False) -> (~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)) -> False) -> (~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)) -> False.
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (@I (a0 -> Prop) x0 x1).
Definition term64 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (@I ((a0 -> Prop) -> Prop) x1 y0).
Definition term32 (a0 : Type') (x0 : type686 a0) (x1 : a0) := imp (forall y0 : a0 -> Prop, (x0 y0) -> y0 x1).
Definition term23 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := imp (forall y0 : a0 -> Prop, (x0 y0) -> x1 y0).
Definition term3 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := imp (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN (a0 -> Prop) y0 x1).
Definition term42 (a0 : Type') := forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2.
Definition term15 (a0 : Type') := forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> @IN (a0 -> Prop) y2 y0) -> forall y2 : a0, (@IN a0 y2 (@INTERS a0 y0)) -> @IN a0 y2 (@INTERS a0 y1).
Definition term14 (a0 : Type') := forall y0 : type686 a0, forall y1 : type686 a0, (@SUBSET (a0 -> Prop) y1 y0) -> @SUBSET a0 (@INTERS a0 y0) (@INTERS a0 y1).
Definition term19 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (x0 x2) -> x1 x2.
Definition term83 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (@I (a0 -> Prop) x2 x0) \/ (~ (@I ((a0 -> Prop) -> Prop) x1 x2)).
Definition term5 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0, (@IN a0 y0 (@INTERS a0 x0)) -> @IN a0 y0 (@INTERS a0 x1).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@I (a0 -> Prop) x0 x1) -> False.
Definition term38 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (forall y0 : a0 -> Prop, (x1 y0) -> x0 y0) -> forall y0 : a0, (forall y1 : a0 -> Prop, (x0 y1) -> y1 y0) -> forall y1 : a0 -> Prop, (x1 y1) -> y1 y0.
Definition term34 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (forall y0 : a0 -> Prop, (x0 y0) -> y0 x2) -> forall y0 : a0 -> Prop, (x1 y0) -> y0 x2.
Definition term84 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (@I (a0 -> Prop) x1 x2)).
Definition term10 (a0 : Type') (x0 : type686 a0) := forall y0 : type686 a0, (@SUBSET (a0 -> Prop) y0 x0) -> @SUBSET a0 (@INTERS a0 x0) (@INTERS a0 y0).
Definition term74 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (@I ((a0 -> Prop) -> Prop) x0 x2) \/ (~ (@I ((a0 -> Prop) -> Prop) x1 x2)).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term39 (a0 : Type') (x0 : type686 a0) := fun y0 : type686 a0 => (forall y1 : a0 -> Prop, (y0 y1) -> x0 y1) -> forall y1 : a0, (forall y2 : a0 -> Prop, (x0 y2) -> y2 y1) -> forall y2 : a0 -> Prop, (y0 y2) -> y2 y1.
Definition term9 (a0 : Type') (x0 : type686 a0) := fun y0 : type686 a0 => (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> @IN (a0 -> Prop) y1 x0) -> forall y1 : a0, (@IN a0 y1 (@INTERS a0 x0)) -> @IN a0 y1 (@INTERS a0 y0).
Definition term4 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := @SUBSET a0 (@INTERS a0 x0) (@INTERS a0 x1).
Definition term40 (a0 : Type') (x0 : type686 a0) := forall y0 : type686 a0, (forall y1 : a0 -> Prop, (y0 y1) -> x0 y1) -> forall y1 : a0, (forall y2 : a0 -> Prop, (x0 y2) -> y2 y1) -> forall y2 : a0 -> Prop, (y0 y2) -> y2 y1.
Definition term11 (a0 : Type') (x0 : type686 a0) := forall y0 : type686 a0, (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> @IN (a0 -> Prop) y1 x0) -> forall y1 : a0, (@IN a0 y1 (@INTERS a0 x0)) -> @IN a0 y1 (@INTERS a0 y0).
Definition term48 (a0 : Type') := (((~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)) -> False) -> (~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)) -> False) -> ((~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)) -> False) -> (~ (forall y0 : type686 a0, forall y1 : type686 a0, (forall y2 : a0 -> Prop, (y1 y2) -> y0 y2) -> forall y2 : a0, (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2) -> forall y3 : a0 -> Prop, (y1 y3) -> y3 y2)) -> False.
Definition term81 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp (@I ((a0 -> Prop) -> Prop) x0 x1).
Definition term59 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (x0 x1).
Definition term58 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (y0 x1).
Definition term27 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 x1) -> x1 x2.
Definition term54 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := fun y0 : a0 -> Prop => (~ (x0 y0)) \/ (x1 y0).
Definition term60 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (@I ((a0 -> Prop) -> Prop) x0 x1).
Definition term67 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (@I (a0 -> Prop) y0 x1).
Definition term22 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (x0 y0) -> x1 y0.
Definition term26 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 x0) -> @IN a0 x1 x2.
Definition term28 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term80 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp (~ (~ (@I ((a0 -> Prop) -> Prop) x0 x1))).