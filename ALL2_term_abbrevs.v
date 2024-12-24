Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term38 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : type1470 a0 a1) (x3 : list a1) (x4 : list a0) := ((@ALL2 a1 a0 x2 (@nil a1) (@nil a0)) = True) /\ (((@ALL2 a1 a0 x2 (@cons a1 x0 x3) (@nil a0)) = False) /\ (((@ALL2 a1 a0 x2 (@nil a1) (@cons a0 x1 x4)) = False) /\ ((@ALL2 a1 a0 x2 (@cons a1 x0 x3) (@cons a0 x1 x4)) = ((x2 x0 x1) /\ (@ALL2 a1 a0 x2 x3 x4))))).
Definition term3 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ ((@nil a0) = (@cons a0 x0 x1)).
Definition term25 (a0 : Type') (x0 : a0) (x1 : list a0) := @hd a0 (@cons a0 x0 x1).
Definition term15 (a0 : Type') (x0 : list a0) (x1 : Prop) (x2 : Prop) := @COND Prop (x0 = x0) x1 x2.
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a0) (x2 : list a0) := and ((@ALL2 a1 a0 x0 (@nil a1) (@cons a0 x1 x2)) = False).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : type1470 a0 a1) (x3 : list a1) (x4 : list a0) := ((@ALL2 a1 a0 x2 (@cons a1 x0 x3) (@nil a0)) = False) /\ (((@ALL2 a1 a0 x2 (@nil a1) (@cons a0 x1 x4)) = False) /\ ((@ALL2 a1 a0 x2 (@cons a1 x0 x3) (@cons a0 x1 x4)) = ((x2 x0 x1) /\ (@ALL2 a1 a0 x2 x3 x4)))).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) (x3 : list a0) := x0 x1 (@hd a0 (@cons a0 x2 x3)).
Definition term24 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND Prop ((@cons a0 x0 x1) = (@nil a0)) False.
Definition term29 (a0 : Type') (x0 : a0) (x1 : list a0) := @tl a0 (@cons a0 x0 x1).
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : list a1) := @ALL2 a1 a0 x0 (@cons a1 x1 x2) (@nil a0).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : list a1) := (x1 x0 (@hd a0 (@nil a0))) /\ (@ALL2 a1 a0 x1 x2 (@tl a0 (@nil a0))).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : type1470 a0 a1) (x3 : list a1) (x4 : list a0) := (x2 x0 x1) /\ (@ALL2 a1 a0 x2 x3 x4).
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : list a1) := ~ (@ALL2 a1 a0 x0 (@cons a1 x1 x2) (@nil a0)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : list a1) (x3 : list a0) := @COND Prop (x3 = (@nil a0)) False ((x1 x0 (@hd a0 x3)) /\ (@ALL2 a1 a0 x1 x2 (@tl a0 x3))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1413 a0 a1) (x2 : list a0) (x3 : list a1) := @COND Prop (x3 = (@nil a1)) False ((x1 x0 (@hd a1 x3)) /\ (@ALL2 a0 a1 x1 x2 (@tl a1 x3))).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : list a1) (x3 : a0) (x4 : list a0) := @ALL2 a1 a0 x0 (@cons a1 x1 x2) (@cons a0 x3 x4).
Definition term30 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : list a1) (x2 : a0) (x3 : list a0) := @ALL2 a1 a0 x0 x1 (@tl a0 (@cons a0 x2 x3)).
Definition term5 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ ((@cons a0 x0 x1) = (@nil a0))) -> ((@cons a0 x0 x1) = (@nil a0)) = False.
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) (x3 : list a0) := and (x0 x1 (@hd a0 (@cons a0 x2 x3))).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : list a1) (x3 : a0) (x4 : list a0) := (x1 x0 (@hd a0 (@cons a0 x3 x4))) /\ (@ALL2 a1 a0 x1 x2 (@tl a0 (@cons a0 x3 x4))).
Definition term2 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => ~ ((@nil a0) = (@cons a0 x0 y0))) x1.
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := and ((@ALL2 a1 a0 x0 (@nil a1) (@nil a0)) = True).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : type1470 a0 a1) (x3 : list a1) (x4 : list a0) := @eq Prop ((x2 x0 x1) /\ (@ALL2 a1 a0 x2 x3 x4)).
Definition term19 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a0) (x2 : list a0) := ~ (@ALL2 a1 a0 x0 (@nil a1) (@cons a0 x1 x2)).
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : list a0, ~ ((@nil a0) = (@cons a0 x0 y0)).
Definition term4 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ ((@cons a0 x0 x1) = (@nil a0)).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : list a1) (x3 : a0) (x4 : list a0) := @COND Prop ((@cons a0 x3 x4) = (@nil a0)) False ((x1 x0 (@hd a0 (@cons a0 x3 x4))) /\ (@ALL2 a1 a0 x1 x2 (@tl a0 (@cons a0 x3 x4)))).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : list a1) := @COND Prop ((@nil a0) = (@nil a0)) False ((x1 x0 (@hd a0 (@nil a0))) /\ (@ALL2 a1 a0 x1 x2 (@tl a0 (@nil a0)))).
Definition term34 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : list a1) (x3 : a0) (x4 : list a0) := @eq Prop (@ALL2 a1 a0 x0 (@cons a1 x1 x2) (@cons a0 x3 x4)).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : type1470 a0 a1) (x3 : list a1) (x4 : list a0) := @COND Prop False False ((x2 x0 x1) /\ (@ALL2 a1 a0 x2 x3 x4)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : type1470 a0 a1) (x3 : list a1) (x4 : list a0) := ((@ALL2 a1 a0 x2 (@nil a1) (@cons a0 x1 x4)) = False) /\ ((@ALL2 a1 a0 x2 (@cons a1 x0 x3) (@cons a0 x1 x4)) = ((x2 x0 x1) /\ (@ALL2 a1 a0 x2 x3 x4))).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a0) (x2 : list a0) := @ALL2 a1 a0 x0 (@nil a1) (@cons a0 x1 x2).
Definition term17 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : list a1) := and ((@ALL2 a1 a0 x0 (@cons a1 x1 x2) (@nil a0)) = False).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := and (x0 x1 x2).
Definition term23 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND Prop ((@cons a0 x0 x1) = (@nil a0)).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, ~ ((@nil a0) = (@cons a0 y0 y1))) x0.
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : list a1) (x3 : list a0) := @ALL2 a1 a0 x0 (@cons a1 x1 x2) x3.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : list a0) (x3 : list a1) := @ALL2 a0 a1 x0 (@cons a0 x1 x2) x3.
