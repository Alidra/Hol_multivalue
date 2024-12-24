Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (a0 : Type') (a1 : Type') := (exists y0 : type1207 a0 a1, forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = y1) -> (fun y0 : type1207 a0 a1 => forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = y1) (@ε ((prod a0 a1) -> a0) (fun y0 : type1207 a0 a1 => forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = y1)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1207 a0 a1) := fun y0 : a0 => forall y1 : a1, (x0 (@pair a0 a1 y0 y1)) = y0.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1207 a0 a1) (x1 : a0) := fun y0 : a1 => (x0 (@pair a0 a1 x1 y0)) = ((fun y1 : a0 => fun y2 : a1 => y1) x1 y0).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => x0) x1.
Definition term22 (a0 : Type') (a1 : Type') := (fun y0 : type1207 a0 a1 => forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = y1) (@ε ((prod a0 a1) -> a0) (fun y0 : type1207 a0 a1 => forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = y1)).
Definition term2 (a0 : Type') (a1 : Type') := fun y0 : a0 => fun y1 : a1 => y0.
Definition term12 (a0 : Type') (a1 : Type') (x0 : type1207 a0 a1) (x1 : a0) := forall y0 : a1, (x0 (@pair a0 a1 x1 y0)) = x1.
Definition term19 (a0 : Type') (a1 : Type') := exists y0 : type1207 a0 a1, forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = y1.
Definition term1 (a0 : Type') (a1 : Type') := exists y0 : type1207 a0 a1, forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = ((fun y3 : a0 => fun y4 : a1 => y3) y1 y2).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1410 a0 a1) := exists y0 : type1207 a0 a1, forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = (x0 y1 y2).
Definition term23 (a0 : Type') (a1 : Type') := forall y0 : a0, forall y1 : a1, (@ε ((prod a0 a1) -> a0) (fun y2 : type1207 a0 a1 => forall y3 : a0, forall y4 : a1, (y2 (@pair a0 a1 y3 y4)) = y3) (@pair a0 a1 y0 y1)) = y0.
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1207 a0 a1) := forall y0 : a0, forall y1 : a1, (x0 (@pair a0 a1 y0 y1)) = y0.
Definition term18 (a0 : Type') (a1 : Type') := fun y0 : type1207 a0 a1 => forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = y1.
Definition term17 (a0 : Type') (a1 : Type') := fun y0 : type1207 a0 a1 => forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = ((fun y3 : a0 => fun y4 : a1 => y3) y1 y2).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@ε ((prod a0 a1) -> a0) (fun y1 : type1207 a0 a1 => forall y2 : a0, forall y3 : a1, (y1 (@pair a0 a1 y2 y3)) = y2) (@pair a0 a1 x0 y0)) = x0) x1.
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@ε ((prod a0 a1) -> a0) (fun y2 : type1207 a0 a1 => forall y3 : a0, forall y4 : a1, (y2 (@pair a0 a1 y3 y4)) = y3) (@pair a0 a1 y0 y1)) = y0) x0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1207 a0 a1) (x1 : a0) (x2 : a1) := x0 (@pair a0 a1 x1 x2).
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1207 a0 a1) (x1 : a0) (x2 : a1) := @eq a0 (x0 (@pair a0 a1 x1 x2)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a0 => fun y1 : a1 => y0) x0 x1.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) := fun y0 : a1 => x0.
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1207 a0 a1) (x1 : a0) := fun y0 : a1 => (x0 (@pair a0 a1 x1 y0)) = x1.
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @ε ((prod a0 a1) -> a0) (fun y0 : type1207 a0 a1 => forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = y1) (@pair a0 a1 x0 x1).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type316 a0 a1) := (ex x0) -> x0 (@ε ((prod a0 a1) -> a0) x0).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@ε ((prod a0 a1) -> a0) (fun y1 : type1207 a0 a1 => forall y2 : a0, forall y3 : a1, (y1 (@pair a0 a1 y2 y3)) = y2) (@pair a0 a1 x0 y0)) = x0.
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1207 a0 a1) := forall y0 : a0, forall y1 : a1, (x0 (@pair a0 a1 y0 y1)) = ((fun y2 : a0 => fun y3 : a1 => y2) y0 y1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1207 a0 a1) := fun y0 : a0 => forall y1 : a1, (x0 (@pair a0 a1 y0 y1)) = ((fun y2 : a0 => fun y3 : a1 => y2) y0 y1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : a1 => y0) x0.
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1207 a0 a1) (x1 : a0) := forall y0 : a1, (x0 (@pair a0 a1 x1 y0)) = ((fun y1 : a0 => fun y2 : a1 => y1) x1 y0).
