Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) := forall y0 : cart a0 a2, (@sndcart a0 a1 a2 (@pastecart a0 a1 a2 x0 y0)) = y0.
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) := @sndcart a0 a1 a2 (@pastecart a0 a1 a2 x0 x1).
Definition term29 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) := fun y0 : cart a0 a2 => forall y1 : cart a0 a1, forall y2 : cart a0 a2, ((@pastecart a0 a1 a2 x0 y0) = (@pastecart a0 a1 a2 y1 y2)) = ((x0 = y1) /\ (y0 = y2)).
Definition term25 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term22 (a0 : Type') (a1 : Type') := fun y0 : cart a0 a1 => True.
Definition term15 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) (x2 : cart a0 a1) (x3 : cart a0 a2) := and ((@fstcart a0 a1 a2 (@pastecart a0 a1 a2 x0 x1)) = (@fstcart a0 a1 a2 (@pastecart a0 a1 a2 x2 x3))).
Definition term31 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : cart a0 a1 => forall y1 : cart a0 a2, forall y2 : cart a0 a1, forall y3 : cart a0 a2, ((@pastecart a0 a1 a2 y0 y1) = (@pastecart a0 a1 a2 y2 y3)) = ((y0 = y2) /\ (y1 = y3)).
Definition term23 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a2) := forall y0 : cart a0 a2, ((@pastecart a0 a1 a2 x0 x2) = (@pastecart a0 a1 a2 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term8 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type3 a0 a1 a2) := (fun y0 : type3 a0 a1 a2 => forall y1 : type3 a0 a1 a2, (y0 = y1) = (((@fstcart a1 a0 a2 y0) = (@fstcart a1 a0 a2 y1)) /\ ((@sndcart a1 a0 a2 y0) = (@sndcart a1 a0 a2 y1)))) x0.
Definition term27 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) := fun y0 : cart a0 a1 => forall y1 : cart a0 a2, ((@pastecart a0 a1 a2 x0 x1) = (@pastecart a0 a1 a2 y0 y1)) = ((x0 = y0) /\ (x1 = y1)).
Definition term28 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) := forall y0 : cart a0 a1, forall y1 : cart a0 a2, ((@pastecart a0 a1 a2 x0 x1) = (@pastecart a0 a1 a2 y0 y1)) = ((x0 = y0) /\ (x1 = y1)).
Definition term14 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) := @eq (cart a0 a1) (@fstcart a0 a1 a2 (@pastecart a0 a1 a2 x0 x1)).
Definition term26 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : cart a0 a1, x0.
Definition term21 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a2) := fun y0 : cart a0 a2 => ((@pastecart a0 a1 a2 x0 x2) = (@pastecart a0 a1 a2 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) := @fstcart a0 a1 a2 (@pastecart a0 a1 a2 x0 x1).
Definition term24 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, True.
Definition term12 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type2 a0 a1 a2) (x1 : type2 a0 a1 a2) := ((@fstcart a0 a1 a2 x0) = (@fstcart a0 a1 a2 x1)) /\ ((@sndcart a0 a1 a2 x0) = (@sndcart a0 a1 a2 x1)).
Definition term11 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type3 a0 a1 a2) (x1 : type3 a0 a1 a2) := ((@fstcart a1 a0 a2 x0) = (@fstcart a1 a0 a2 x1)) /\ ((@sndcart a1 a0 a2 x0) = (@sndcart a1 a0 a2 x1)).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) := forall y0 : cart a0 a2, (@fstcart a0 a1 a2 (@pastecart a0 a1 a2 x0 y0)) = x0.
Definition term16 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := and (x0 = x1).
Definition term10 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type3 a0 a1 a2) (x1 : type3 a0 a1 a2) := (fun y0 : type3 a0 a1 a2 => (x0 = y0) = (((@fstcart a1 a0 a2 x0) = (@fstcart a1 a0 a2 y0)) /\ ((@sndcart a1 a0 a2 x0) = (@sndcart a1 a0 a2 y0)))) x1.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) := (fun y0 : cart a0 a2 => (@sndcart a0 a1 a2 (@pastecart a0 a1 a2 x0 y0)) = y0) x1.
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) := (fun y0 : cart a0 a2 => (@fstcart a0 a1 a2 (@pastecart a0 a1 a2 x0 y0)) = x0) x1.
Definition term9 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type3 a0 a1 a2) := forall y0 : type3 a0 a1 a2, (x0 = y0) = (((@fstcart a1 a0 a2 x0) = (@fstcart a1 a0 a2 y0)) /\ ((@sndcart a1 a0 a2 x0) = (@sndcart a1 a0 a2 y0))).
Definition term18 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a2) (x3 : cart a0 a2) := (x0 = x1) /\ (x2 = x3).
Definition term32 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : cart a0 a1, forall y1 : cart a0 a2, forall y2 : cart a0 a1, forall y3 : cart a0 a2, ((@pastecart a0 a1 a2 y0 y1) = (@pastecart a0 a1 a2 y2 y3)) = ((y0 = y2) /\ (y1 = y3)).
Definition term30 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) := forall y0 : cart a0 a2, forall y1 : cart a0 a1, forall y2 : cart a0 a2, ((@pastecart a0 a1 a2 x0 y0) = (@pastecart a0 a1 a2 y1 y2)) = ((x0 = y1) /\ (y0 = y2)).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) := (fun y0 : cart a0 a1 => forall y1 : cart a0 a2, (@fstcart a0 a1 a2 (@pastecart a0 a1 a2 y0 y1)) = y0) x0.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) := (fun y0 : cart a0 a1 => forall y1 : cart a0 a2, (@sndcart a0 a1 a2 (@pastecart a0 a1 a2 y0 y1)) = y1) x0.
Definition term17 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) := @eq (cart a0 a2) (@sndcart a0 a1 a2 (@pastecart a0 a1 a2 x0 x1)).
Definition term19 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) (x2 : cart a0 a1) (x3 : cart a0 a2) := @eq Prop ((@pastecart a0 a1 a2 x0 x1) = (@pastecart a0 a1 a2 x2 x3)).
Definition term20 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) (x2 : cart a0 a2) (x3 : cart a0 a2) := @eq Prop ((x0 = x1) /\ (x2 = x3)).
Definition term13 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : cart a0 a1) (x1 : cart a0 a2) (x2 : cart a0 a1) (x3 : cart a0 a2) := ((@fstcart a0 a1 a2 (@pastecart a0 a1 a2 x0 x1)) = (@fstcart a0 a1 a2 (@pastecart a0 a1 a2 x2 x3))) /\ ((@sndcart a0 a1 a2 (@pastecart a0 a1 a2 x0 x1)) = (@sndcart a0 a1 a2 (@pastecart a0 a1 a2 x2 x3))).
