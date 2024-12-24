Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a1) := forall y0 : type24 a0 a2, (@PCROSS a0 a1 a2 (@INTERS (cart a0 a1) x0) y0) = (@COND ((cart a0 (finite_sum a1 a2)) -> Prop) (x0 = (@EMPTY ((cart a0 a1) -> Prop))) (@PCROSS a0 a1 a2 (@UNIV (cart a0 a1)) y0) (@INTERS (cart a0 (finite_sum a1 a2)) (@GSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) (fun y1 : type16 a0 a1 a2 => exists y2 : type24 a0 a1, @SETSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) y1 (@IN ((cart a0 a1) -> Prop) y2 x0) (@PCROSS a0 a1 a2 y2 y0))))).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type56 a0 a1, forall y1 : type24 a0 a2, (@PCROSS a0 a1 a2 (@INTERS (cart a0 a1) y0) y1) = (@COND ((cart a0 (finite_sum a1 a2)) -> Prop) (y0 = (@EMPTY ((cart a0 a1) -> Prop))) (@PCROSS a0 a1 a2 (@UNIV (cart a0 a1)) y1) (@INTERS (cart a0 (finite_sum a1 a2)) (@GSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) (fun y2 : type16 a0 a1 a2 => exists y3 : type24 a0 a1, @SETSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) y2 (@IN ((cart a0 a1) -> Prop) y3 y0) (@PCROSS a0 a1 a2 y3 y1))))).
