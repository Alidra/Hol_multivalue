Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term33 (a0 : Type') := fun y0 : type686 a0 => forall y1 : a0 -> Prop, (y0 y1) -> @UNION_OF a0 (@ARBITRARY a0) y0 y1.
Definition term19 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ((@ARBITRARY a0 (@INSERT (a0 -> Prop) x1 (@EMPTY (a0 -> Prop)))) /\ (x0 x1)) -> (@UNION_OF a0 (@ARBITRARY a0) x0 x1) = True.
Definition term31 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := ((x0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) /\ (x1 x2)) -> (@UNION_OF a0 x0 x1 x2) = True.
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term29 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (x0 y0) -> @UNION_OF a0 (@ARBITRARY a0) x0 y0.
Definition term3 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := (fun y0 : type686 a0 => forall y1 : a0 -> Prop, ((x0 (@INSERT (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) /\ (y0 y1)) -> @UNION_OF a0 x0 y0 y1) x1.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := and (@ARBITRARY a0 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))).
Definition term23 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (x0 x1) -> (@UNION_OF a0 (@ARBITRARY a0) x0 x1) = True.
Definition term7 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (x0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) /\ (x1 x2).
Definition term4 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, ((x0 (@INSERT (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))) /\ (x1 y0)) -> @UNION_OF a0 x0 x1 y0.
Definition term0 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (@ARBITRARY a0 y0) = True) x0.
Definition term6 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := ((x0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) /\ (x1 x2)) -> @UNION_OF a0 x0 x1 x2.
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term17 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) := ((x0 x1) -> (@UNION_OF a0 (@ARBITRARY a0) x0 x1) = x2) -> ((x0 x1) -> @UNION_OF a0 (@ARBITRARY a0) x0 x1) = ((x0 x1) -> x2).
Definition term36 (a0 : Type') := forall y0 : type686 a0, True.
Definition term14 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((x0 x1) = x2) -> (x2 -> (@UNION_OF a0 (@ARBITRARY a0) x0 x1) = y0) -> ((x0 x1) -> @UNION_OF a0 (@ARBITRARY a0) x0 x1) = (x2 -> y0)) x3.
Definition term5 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((x0 (@INSERT (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))) /\ (x1 y0)) -> @UNION_OF a0 x0 x1 y0) x2.
Definition term34 (a0 : Type') := fun y0 : type686 a0 => True.
Definition term13 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) := forall y0 : Prop, ((x0 x1) = x2) -> (x2 -> (@UNION_OF a0 (@ARBITRARY a0) x0 x1) = y0) -> ((x0 x1) -> @UNION_OF a0 (@ARBITRARY a0) x0 x1) = (x2 -> y0).
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term28 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term22 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (@ARBITRARY a0 (@INSERT (a0 -> Prop) x1 (@EMPTY (a0 -> Prop)))) /\ (x0 x1).
Definition term16 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) := ((x0 x1) = (x0 x1)) -> ((x0 x1) -> (@UNION_OF a0 (@ARBITRARY a0) x0 x1) = x2) -> ((x0 x1) -> @UNION_OF a0 (@ARBITRARY a0) x0 x1) = ((x0 x1) -> x2).
Definition term11 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((x0 x1) = y0) -> (y0 -> (@UNION_OF a0 (@ARBITRARY a0) x0 x1) = y1) -> ((x0 x1) -> @UNION_OF a0 (@ARBITRARY a0) x0 x1) = (y0 -> y1).
Definition term10 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term35 (a0 : Type') := forall y0 : type686 a0, forall y1 : a0 -> Prop, (y0 y1) -> @UNION_OF a0 (@ARBITRARY a0) y0 y1.
Definition term2 (a0 : Type') (x0 : type180 a0) := forall y0 : type686 a0, forall y1 : a0 -> Prop, ((x0 (@INSERT (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) /\ (y0 y1)) -> @UNION_OF a0 x0 y0 y1.
Definition term24 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ((x0 x1) -> (@UNION_OF a0 (@ARBITRARY a0) x0 x1) = True) -> ((x0 x1) -> @UNION_OF a0 (@ARBITRARY a0) x0 x1) = ((x0 x1) -> True).
Definition term37 (a0 : Type') (x0 : Prop) := forall y0 : type686 a0, x0.
Definition term15 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) (x3 : Prop) := ((x0 x1) = x2) -> (x2 -> (@UNION_OF a0 (@ARBITRARY a0) x0 x1) = x3) -> ((x0 x1) -> @UNION_OF a0 (@ARBITRARY a0) x0 x1) = (x2 -> x3).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := @ARBITRARY a0 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))).
Definition term27 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (x0 y0) -> @UNION_OF a0 (@ARBITRARY a0) x0 y0.
Definition term12 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 x1) = y0) -> (y0 -> (@UNION_OF a0 (@ARBITRARY a0) x0 x1) = y1) -> ((x0 x1) -> @UNION_OF a0 (@ARBITRARY a0) x0 x1) = (y0 -> y1)) x2.
Definition term26 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (x0 x1) -> True.
Definition term30 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term25 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (x0 x1) -> @UNION_OF a0 (@ARBITRARY a0) x0 x1.
Definition term1 (a0 : Type') (x0 : type180 a0) := (fun y0 : type180 a0 => forall y1 : type686 a0, forall y2 : a0 -> Prop, ((y0 (@INSERT (a0 -> Prop) y2 (@EMPTY (a0 -> Prop)))) /\ (y1 y2)) -> @UNION_OF a0 y0 y1 y2) x0.