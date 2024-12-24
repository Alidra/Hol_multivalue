Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term32 (a0 : Type') := fun y0 : type686 a0 => forall y1 : a0 -> Prop, (@INTERSECTION_OF a0 (@ARBITRARY a0) y0 y1) = (@INTERSECTION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y2))) (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y1))).
Definition term31 (a0 : Type') := fun y0 : type686 a0 => forall y1 : a0 -> Prop, (@INTERSECTION_OF a0 (@ARBITRARY a0) y0 y1) = (@UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)).
Definition term15 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0)) x1.
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term12 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => x0 y0) x1.
Definition term27 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0) = (@UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)).
Definition term18 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) y0) (@DIFF a0 (@UNIV a0) x1)).
Definition term9 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @INTERSECTION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)) (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) x1)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term39 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term7 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @INTERSECTION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0)) (@DIFF a0 (@UNIV a0) x1).
Definition term13 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) y0) (@DIFF a0 (@UNIV a0) x1).
Definition term26 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop (@INTERSECTION_OF a0 (@ARBITRARY a0) x0 x1).
Definition term21 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0).
Definition term23 (a0 : Type') (x0 : type686 a0) := @INTERSECTION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)).
Definition term30 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0) = (@INTERSECTION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y1))) (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y0))).
Definition term17 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) y0.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y0)) = y0) x0.
Definition term22 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y0)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term41 (a0 : Type') := forall y0 : type686 a0, True.
Definition term16 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := x0 (@DIFF a0 (@UNIV a0) x1).
Definition term35 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => x0 y0.
Definition term40 (a0 : Type') := fun y0 : type686 a0 => True.
Definition term10 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := @DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) x0).
Definition term19 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0)) (@DIFF a0 (@UNIV a0) x1)).
Definition term36 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term4 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => forall y1 : a0 -> Prop, (@UNION_OF a0 (@ARBITRARY a0) y0 y1) = (@INTERSECTION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1))) x0.
Definition term28 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0) = (@INTERSECTION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y1))) (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y0))).
Definition term34 (a0 : Type') := forall y0 : type686 a0, forall y1 : a0 -> Prop, (@INTERSECTION_OF a0 (@ARBITRARY a0) y0 y1) = (@INTERSECTION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y2))) (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y1))).
Definition term33 (a0 : Type') := forall y0 : type686 a0, forall y1 : a0 -> Prop, (@INTERSECTION_OF a0 (@ARBITRARY a0) y0 y1) = (@UNION_OF a0 (@ARBITRARY a0) (fun y2 : a0 -> Prop => y0 (@DIFF a0 (@UNIV a0) y2)) (@DIFF a0 (@UNIV a0) y1)).
Definition term42 (a0 : Type') (x0 : Prop) := forall y0 : type686 a0, x0.
Definition term14 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0)) (@DIFF a0 (@UNIV a0) x1).
Definition term29 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@INTERSECTION_OF a0 (@ARBITRARY a0) x0 y0) = (@UNION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)).
Definition term5 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@UNION_OF a0 (@ARBITRARY a0) x0 y0) = (@INTERSECTION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0)).
Definition term20 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := x0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) x1)).
Definition term6 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@UNION_OF a0 (@ARBITRARY a0) x0 y0) = (@INTERSECTION_OF a0 (@ARBITRARY a0) (fun y1 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y1)) (@DIFF a0 (@UNIV a0) y0))) x1.
Definition term24 (a0 : Type') (x0 : type686 a0) := @INTERSECTION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y0))).
Definition term8 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @UNION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) y0)) (@DIFF a0 (@UNIV a0) x1).
Definition term25 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @INTERSECTION_OF a0 (@ARBITRARY a0) (fun y0 : a0 -> Prop => x0 (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) y0))) (@DIFF a0 (@UNIV a0) (@DIFF a0 (@UNIV a0) x1)).
Definition term37 (a0 : Type') := forall y0 : a0 -> Prop, True.
