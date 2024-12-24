Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1413 a0 a1) (x2 : list a0) := (fun y0 : list a0 => forall y1 : list a1, (@ALL2 a0 a1 x1 (@cons a0 x0 y0) y1) = (@COND Prop (y1 = (@nil a1)) False ((x1 x0 (@hd a1 y1)) /\ (@ALL2 a0 a1 x1 y0 (@tl a1 y1))))) x2.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1413 a0 a1) (x2 : list a0) := forall y0 : list a1, (@ALL2 a0 a1 x1 (@cons a0 x0 x2) y0) = (@COND Prop (y0 = (@nil a1)) False ((x1 x0 (@hd a1 y0)) /\ (@ALL2 a0 a1 x1 x2 (@tl a1 y0)))).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : type1413 a0 a1, forall y1 : list a0, forall y2 : list a1, (@ALL2 a0 a1 y0 (@cons a0 x0 y1) y2) = (@COND Prop (y2 = (@nil a1)) False ((y0 x0 (@hd a1 y2)) /\ (@ALL2 a0 a1 y0 y1 (@tl a1 y2)))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1413 a0 a1) := forall y0 : list a0, forall y1 : list a1, (@ALL2 a0 a1 x1 (@cons a0 x0 y0) y1) = (@COND Prop (y1 = (@nil a1)) False ((x1 x0 (@hd a1 y1)) /\ (@ALL2 a0 a1 x1 y0 (@tl a1 y1)))).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => forall y1 : list a0, forall y2 : list a1, (@ALL2 a0 a1 y0 (@cons a0 x0 y1) y2) = (@COND Prop (y2 = (@nil a1)) False ((y0 x0 (@hd a1 y2)) /\ (@ALL2 a0 a1 y0 y1 (@tl a1 y2))))) x1.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1413 a0 a1) (x2 : list a0) (x3 : list a1) := (fun y0 : list a1 => (@ALL2 a0 a1 x1 (@cons a0 x0 x2) y0) = (@COND Prop (y0 = (@nil a1)) False ((x1 x0 (@hd a1 y0)) /\ (@ALL2 a0 a1 x1 x2 (@tl a1 y0))))) x3.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1413 a0 a1, forall y2 : list a0, forall y3 : list a1, (@ALL2 a0 a1 y1 (@cons a0 y0 y2) y3) = (@COND Prop (y3 = (@nil a1)) False ((y1 y0 (@hd a1 y3)) /\ (@ALL2 a0 a1 y1 y2 (@tl a1 y3))))) x0.
