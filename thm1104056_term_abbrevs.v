Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1413 a0 a1) (x2 : list a0) (x3 : list a1) := @COND Prop (x3 = (@nil a1)) False ((x1 x0 (@hd a1 x3)) /\ (@ALL2 a0 a1 x1 x2 (@tl a1 x3))).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1413 a0 a1) (x2 : list a0) (x3 : list a1) := (fun y0 : list a1 => (@ALL2 a0 a1 x1 (@cons a0 x0 x2) y0) = (@COND Prop (y0 = (@nil a1)) False ((x1 x0 (@hd a1 y0)) /\ (@ALL2 a0 a1 x1 x2 (@tl a1 y0))))) x3.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : list a0) (x3 : list a1) := @ALL2 a0 a1 x0 (@cons a0 x1 x2) x3.
