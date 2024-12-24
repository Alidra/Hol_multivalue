Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2 -> Prop) (x1 : type1514 a0 a1 a2) := (fun y0 : type1514 a0 a1 a2 => fun y1 : a2 -> a0 => @RESTRICTION a2 a1 x0 (fun y2 : a2 => y0 y2 (y1 y2))) x1.
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2 -> Prop) (x1 : type1514 a0 a1 a2) := fun y0 : a2 -> a0 => @RESTRICTION a2 a1 x0 (fun y1 : a2 => x1 y1 (y0 y1)).
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2 -> Prop) := fun y0 : type1514 a0 a1 a2 => fun y1 : a2 -> a0 => @RESTRICTION a2 a1 x0 (fun y2 : a2 => y0 y2 (y1 y2)).
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : a2 -> Prop, forall y1 : type1514 a0 a1 a2, (@product_map a0 a1 a2 y0 y1) = (fun y2 : a2 -> a0 => @RESTRICTION a2 a1 y0 (fun y3 : a2 => y1 y3 (y2 y3))).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2 -> Prop) := forall y0 : type1514 a0 a1 a2, (@product_map a0 a1 a2 x0 y0) = (fun y1 : a2 -> a0 => @RESTRICTION a2 a1 x0 (fun y2 : a2 => y0 y2 (y1 y2))).
Definition term8 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2 -> Prop) (x1 : type1514 a0 a1 a2) := (fun y0 : type1514 a0 a1 a2 => (@product_map a0 a1 a2 x0 y0) = (fun y1 : a2 -> a0 => @RESTRICTION a2 a1 x0 (fun y2 : a2 => y0 y2 (y1 y2)))) x1.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : a2 -> Prop => fun y1 : type1514 a0 a1 a2 => fun y2 : a2 -> a0 => @RESTRICTION a2 a1 y0 (fun y3 : a2 => y1 y3 (y2 y3)).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2 -> Prop) := (fun y0 : a2 -> Prop => forall y1 : type1514 a0 a1 a2, (@product_map a0 a1 a2 y0 y1) = (fun y2 : a2 -> a0 => @RESTRICTION a2 a1 y0 (fun y3 : a2 => y1 y3 (y2 y3)))) x0.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2 -> Prop) := (fun y0 : a2 -> Prop => fun y1 : type1514 a0 a1 a2 => fun y2 : a2 -> a0 => @RESTRICTION a2 a1 y0 (fun y3 : a2 => y1 y3 (y2 y3))) x0.
