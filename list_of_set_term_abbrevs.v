Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') := forall y0 : a0 -> Prop, (@list_of_set a0 y0) = (@ε (list a0) (fun y1 : list a0 => ((@set_of_list a0 y1) = y0) /\ ((@List.length a0 y1) = (@CARD a0 y0)))).
Definition term0 (a0 : Type') := fun y0 : a0 -> Prop => @ε (list a0) (fun y1 : list a0 => ((@set_of_list a0 y1) = y0) /\ ((@List.length a0 y1) = (@CARD a0 y0))).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@list_of_set a0 y0) = (@ε (list a0) (fun y1 : list a0 => ((@set_of_list a0 y1) = y0) /\ ((@List.length a0 y1) = (@CARD a0 y0))))) x0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => @ε (list a0) (fun y1 : list a0 => ((@set_of_list a0 y1) = y0) /\ ((@List.length a0 y1) = (@CARD a0 y0)))) x0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := @ε (list a0) (fun y0 : list a0 => ((@set_of_list a0 y0) = x0) /\ ((@List.length a0 y0) = (@CARD a0 x0))).
