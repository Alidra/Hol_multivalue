Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : type24 a0 a1) := @COND ((cart a0 (finite_sum a1 a2)) -> Prop) (x0 = (@EMPTY ((cart a0 a2) -> Prop))) (@PCROSS a0 a1 a2 x1 (@UNIV (cart a0 a2))) (@INTERS (cart a0 (finite_sum a1 a2)) (@GSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) (fun y0 : type16 a0 a1 a2 => exists y1 : type24 a0 a2, @SETSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) y0 (@IN ((cart a0 a2) -> Prop) y1 x0) (@PCROSS a0 a1 a2 x1 y1)))).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : type24 a0 a1) := ((x0 = (@EMPTY ((cart a0 a2) -> Prop))) -> (@PCROSS a0 a1 a2 x1 (@INTERS (cart a0 a2) x0)) = (@PCROSS a0 a1 a2 x1 (@UNIV (cart a0 a2)))) /\ ((~ (x0 = (@EMPTY ((cart a0 a2) -> Prop)))) -> (@PCROSS a0 a1 a2 x1 (@INTERS (cart a0 a2) x0)) = (@INTERS (cart a0 (finite_sum a1 a2)) (@GSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) (fun y0 : type16 a0 a1 a2 => exists y1 : type24 a0 a2, @SETSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) y0 (@IN ((cart a0 a2) -> Prop) y1 x0) (@PCROSS a0 a1 a2 x1 y1))))).
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : type24 a0 a1) := @INTERS (cart a0 (finite_sum a1 a2)) (@GSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) (fun y0 : type16 a0 a1 a2 => exists y1 : type24 a0 a2, @SETSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) y0 (@IN ((cart a0 a2) -> Prop) y1 x0) (@PCROSS a0 a1 a2 x1 y1))).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : type24 a0 a1) := (x0 = (@EMPTY ((cart a0 a2) -> Prop))) -> (@PCROSS a0 a1 a2 x1 (@INTERS (cart a0 a2) x0)) = (@PCROSS a0 a1 a2 x1 (@UNIV (cart a0 a2))).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type56 a0 a1) := ~ (x0 = (@EMPTY ((cart a0 a1) -> Prop))).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a1) (x1 : type56 a0 a2) := @PCROSS a0 a1 a2 x0 (@INTERS (cart a0 a2) x1).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type56 a0 a2) (x1 : type24 a0 a1) := (~ (x0 = (@EMPTY ((cart a0 a2) -> Prop)))) -> (@PCROSS a0 a1 a2 x1 (@INTERS (cart a0 a2) x0)) = (@INTERS (cart a0 (finite_sum a1 a2)) (@GSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) (fun y0 : type16 a0 a1 a2 => exists y1 : type24 a0 a2, @SETSPEC ((cart a0 (finite_sum a1 a2)) -> Prop) y0 (@IN ((cart a0 a2) -> Prop) y1 x0) (@PCROSS a0 a1 a2 x1 y1)))).