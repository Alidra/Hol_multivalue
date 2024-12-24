Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (a0 : Type') (x0 : type1342 a0) (x1 : finite_sum a0 a0) := @eq (finite_sum a0 a0) (x0 (@mktybit0 a0 x1)).
Definition term7 (a0 : Type') := fun y0 : finite_sum a0 a0 => y0.
Definition term11 (a0 : Type') (x0 : type1342 a0) := fun y0 : finite_sum a0 a0 => (x0 (@mktybit0 a0 y0)) = y0.
Definition term13 (a0 : Type') := fun y0 : type1342 a0 => forall y1 : finite_sum a0 a0, (y0 (@mktybit0 a0 y1)) = ((fun y2 : finite_sum a0 a0 => y2) y1).
Definition term0 (a0 : Type') (x0 : type1342 a0) := forall y0 : finite_sum a0 a0, (x0 (@mktybit0 a0 y0)) = y0.
Definition term17 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := ((@mktybit0 a0 x0) = (@mktybit0 a0 x1)) -> x0 = x1.
Definition term6 (a0 : Type') := exists y0 : type1342 a0, forall y1 : finite_sum a0 a0, (y0 (@mktybit0 a0 y1)) = ((fun y2 : finite_sum a0 a0 => y2) y1).
Definition term5 (a0 : Type') (x0 : type43 a0) := exists y0 : type1342 a0, forall y1 : finite_sum a0 a0, (y0 (@mktybit0 a0 y1)) = (x0 y1).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type47 a0 a1) := exists y0 : type1344 a0 a1, forall y1 : finite_sum a0 a0, (y0 (@mktybit0 a0 y1)) = (x0 y1).
Definition term12 (a0 : Type') (x0 : type1342 a0) := forall y0 : finite_sum a0 a0, (x0 (@mktybit0 a0 y0)) = ((fun y1 : finite_sum a0 a0 => y1) y0).
Definition term19 (a0 : Type') (x0 : finite_sum a0 a0) := forall y0 : finite_sum a0 a0, ((@mktybit0 a0 x0) = (@mktybit0 a0 y0)) = (x0 = y0).
Definition term10 (a0 : Type') (x0 : type1342 a0) := fun y0 : finite_sum a0 a0 => (x0 (@mktybit0 a0 y0)) = ((fun y1 : finite_sum a0 a0 => y1) y0).
Definition term1 (a0 : Type') (x0 : type1342 a0) (x1 : finite_sum a0 a0) := (fun y0 : finite_sum a0 a0 => (x0 (@mktybit0 a0 y0)) = y0) x1.
Definition term20 (a0 : Type') := forall y0 : finite_sum a0 a0, forall y1 : finite_sum a0 a0, ((@mktybit0 a0 y0) = (@mktybit0 a0 y1)) = (y0 = y1).
Definition term16 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := (x0 = x1) -> (@mktybit0 a0 x0) = (@mktybit0 a0 x1).
Definition term14 (a0 : Type') := fun y0 : type1342 a0 => forall y1 : finite_sum a0 a0, (y0 (@mktybit0 a0 y1)) = y1.
Definition term3 (a0 : Type') (a1 : Type') (x0 : type47 a0 a1) := (fun y0 : type47 a0 a1 => exists y1 : type1344 a0 a1, forall y2 : finite_sum a0 a0, (y1 (@mktybit0 a0 y2)) = (y0 y2)) x0.
Definition term8 (a0 : Type') (x0 : finite_sum a0 a0) := (fun y0 : finite_sum a0 a0 => y0) x0.
Definition term18 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := (((@mktybit0 a0 x0) = (@mktybit0 a0 x1)) -> x0 = x1) /\ ((x0 = x1) -> (@mktybit0 a0 x0) = (@mktybit0 a0 x1)).
Definition term2 (a0 : Type') (x0 : type1342 a0) (x1 : finite_sum a0 a0) := x0 (@mktybit0 a0 x1).
Definition term15 (a0 : Type') := exists y0 : type1342 a0, forall y1 : finite_sum a0 a0, (y0 (@mktybit0 a0 y1)) = y1.
