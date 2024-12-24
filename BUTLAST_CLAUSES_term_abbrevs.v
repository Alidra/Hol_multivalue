Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => ~ ((@cons a0 x0 y0) = (@nil a0))) x1.
Definition term12 (a0 : Type') (x0 : list a0) (x1 : list a0) (x2 : list a0) := @COND (list a0) (x0 = x0) x1 x2.
Definition term35 (a0 : Type') (x0 : a0) := fun y0 : a0 => forall y1 : list a0, (@List.removelast a0 (@cons a0 x0 (@cons a0 y0 y1))) = (@cons a0 x0 (@List.removelast a0 (@cons a0 y0 y1))).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @List.removelast a0 (@cons a0 x0 (@cons a0 x1 x2)).
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term7 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.removelast a0 (@cons a0 x0 x1).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : list a0 => (@List.removelast a0 (@cons a0 x0 (@cons a0 x1 y0))) = (@cons a0 x0 (@List.removelast a0 (@cons a0 x1 y0))).
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : list a0, ~ ((@cons a0 x0 y0) = (@nil a0)).
Definition term18 (a0 : Type') := forall y0 : a0, True.
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @eq (list a0) (@List.removelast a0 (@cons a0 x0 (@cons a0 x1 x2))).
Definition term14 (a0 : Type') (x0 : a0) := @eq (list a0) (@List.removelast a0 (@cons a0 x0 (@nil a0))).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, ~ ((@cons a0 y0 y1) = (@nil a0))) x0.
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @eq (list a0) (@cons a0 x0 (@COND (list a0) (x2 = (@nil a0)) (@nil a0) (@cons a0 x1 (@List.removelast a0 x2)))).
Definition term10 (a0 : Type') (x0 : a0) := @COND (list a0) ((@nil a0) = (@nil a0)) (@nil a0) (@cons a0 x0 (@List.removelast a0 (@nil a0))).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @cons a0 x0 (@COND (list a0) (x2 = (@nil a0)) (@nil a0) (@cons a0 x1 (@List.removelast a0 x2))).
Definition term37 (a0 : Type') := fun y0 : a0 => forall y1 : a0, forall y2 : list a0, (@List.removelast a0 (@cons a0 y0 (@cons a0 y1 y2))) = (@cons a0 y0 (@List.removelast a0 (@cons a0 y1 y2))).
Definition term33 (a0 : Type') := forall y0 : list a0, True.
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @COND (list a0) ((@cons a0 x1 x2) = (@nil a0)) (@nil a0) (@cons a0 x0 (@List.removelast a0 (@cons a0 x1 x2))).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term4 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ ((@cons a0 x0 x1) = (@nil a0))) -> ((@cons a0 x0 x1) = (@nil a0)) = False.
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : list a0, (@List.removelast a0 (@cons a0 x0 (@cons a0 x1 y0))) = (@cons a0 x0 (@List.removelast a0 (@cons a0 x1 y0))).
Definition term24 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND (list a0) ((@cons a0 x0 x1) = (@nil a0)) (@nil a0).
Definition term15 (a0 : Type') := fun y0 : a0 => (@List.removelast a0 (@cons a0 y0 (@nil a0))) = (@nil a0).
Definition term16 (a0 : Type') := fun y0 : a0 => True.
Definition term13 (a0 : Type') (x0 : a0) := @cons a0 x0 (@List.removelast a0 (@nil a0)).
Definition term38 (a0 : Type') := forall y0 : a0, forall y1 : a0, forall y2 : list a0, (@List.removelast a0 (@cons a0 y0 (@cons a0 y1 y2))) = (@cons a0 y0 (@List.removelast a0 (@cons a0 y1 y2))).
Definition term40 (a0 : Type') := ((@List.removelast a0 (@nil a0)) = (@nil a0)) /\ ((forall y0 : a0, (@List.removelast a0 (@cons a0 y0 (@nil a0))) = (@nil a0)) /\ (forall y0 : a0, forall y1 : a0, forall y2 : list a0, (@List.removelast a0 (@cons a0 y0 (@cons a0 y1 y2))) = (@cons a0 y0 (@List.removelast a0 (@cons a0 y1 y2))))).
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @COND (list a0) False (@nil a0) (@cons a0 x0 (@COND (list a0) (x2 = (@nil a0)) (@nil a0) (@cons a0 x1 (@List.removelast a0 x2)))).
Definition term5 (a0 : Type') := @eq (list a0) (@List.removelast a0 (@nil a0)).
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @cons a0 x0 (@List.removelast a0 (@cons a0 x1 x2)).
Definition term39 (a0 : Type') := (forall y0 : a0, (@List.removelast a0 (@cons a0 y0 (@nil a0))) = (@nil a0)) /\ (forall y0 : a0, forall y1 : a0, forall y2 : list a0, (@List.removelast a0 (@cons a0 y0 (@cons a0 y1 y2))) = (@cons a0 y0 (@List.removelast a0 (@cons a0 y1 y2)))).
Definition term3 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ ((@cons a0 x0 x1) = (@nil a0)).
Definition term8 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND (list a0) (x1 = (@nil a0)) (@nil a0) (@cons a0 x0 (@List.removelast a0 x1)).
Definition term17 (a0 : Type') := forall y0 : a0, (@List.removelast a0 (@cons a0 y0 (@nil a0))) = (@nil a0).
Definition term31 (a0 : Type') := fun y0 : list a0 => True.
Definition term6 (a0 : Type') := and ((@List.removelast a0 (@nil a0)) = (@nil a0)).
Definition term34 (a0 : Type') (x0 : Prop) := forall y0 : list a0, x0.
Definition term9 (a0 : Type') (x0 : a0) := @List.removelast a0 (@cons a0 x0 (@nil a0)).
Definition term36 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : list a0, (@List.removelast a0 (@cons a0 x0 (@cons a0 y0 y1))) = (@cons a0 x0 (@List.removelast a0 (@cons a0 y0 y1))).
Definition term23 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND (list a0) ((@cons a0 x0 x1) = (@nil a0)).
Definition term20 (a0 : Type') := and (forall y0 : a0, (@List.removelast a0 (@cons a0 y0 (@nil a0))) = (@nil a0)).
