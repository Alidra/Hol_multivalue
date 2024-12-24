Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0.
Definition term2 (a0 : Type') (a1 : Type') := exists y0 : type35 a0 a1, True.
Definition term4 (a0 : Type') (a1 : Type') := fun y0 : type62 a0 a1 => y0 (@ε ((finite_image a1) -> a0) y0).
Definition term3 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term6 (a0 : Type') (a1 : Type') := (fun y0 : type62 a0 a1 => y0 (@ε ((finite_image a1) -> a0) y0)) (fun y0 : type35 a0 a1 => True).
Definition term8 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := @mk_cart a0 a1 (@dest_cart a0 a1 x0).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) := @dest_cart a0 a1 (@mk_cart a0 a1 x0).
Definition term12 (a0 : Type') (a1 : Type') := forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0).
Definition term0 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term7 (a0 : Type') (a1 : Type') := (fun y0 : type35 a0 a1 => True) (@ε ((finite_image a1) -> a0) (fun y0 : type35 a0 a1 => True)).
Definition term14 (a0 : Type') (a1 : Type') := (forall y0 : cart a0 a1, (@mk_cart a0 a1 (@dest_cart a0 a1 y0)) = y0) /\ (forall y0 : type35 a0 a1, True = ((@dest_cart a0 a1 (@mk_cart a0 a1 y0)) = y0)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) := @eq Prop ((fun y0 : type35 a0 a1 => True) x0).
Definition term9 (a0 : Type') (a1 : Type') (x0 : type35 a0 a1) := (fun y0 : type35 a0 a1 => True) x0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : Prop) := exists y0 : type35 a0 a1, x0.
Definition term5 (a0 : Type') (a1 : Type') := fun y0 : type35 a0 a1 => True.
