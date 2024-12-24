Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (a4 : Type') (a5 : Type') := (forall y0 : type24 a0 a1, forall y1 : type56 a0 a2, (@PCROSS a0 a1 a2 y0 (@UNIONS (cart a0 a2) y1)) = (@UNIONS (cart a0 (finite_sum a1 a2)) (@GSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) (fun y2 : type16 a0 a1 a2 => exists y3 : type24 a0 a2, @SETSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) y2 (@IN ((cart a0 a2) -> Prop) y3 y1) (@PCROSS a0 a1 a2 y0 y3))))) /\ (forall y0 : type56 a3 a4, forall y1 : type24 a3 a5, (@PCROSS a3 a4 a5 (@UNIONS (cart a3 a4) y0) y1) = (@UNIONS (cart a3 (finite_sum a4 a5)) (@GSPEC ((cart a3 (finite_sum a4 a5)) -> Prop) (fun y2 : type16 a3 a4 a5 => exists y3 : type24 a3 a4, @SETSPEC ((cart a3 (finite_sum a4 a5)) -> Prop) y2 (@IN ((cart a3 a4) -> Prop) y3 y0) (@PCROSS a3 a4 a5 y3 y1))))).
