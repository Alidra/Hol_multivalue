Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term42 (a0 : Type') := forall y0 : a0, forall y1 : list a0, forall y2 : a0, forall y3 : list a0, ((@cons a0 y0 y1) = (@cons a0 y2 y3)) = ((y0 = y2) /\ (y1 = y3)).
Definition term3 (a0 : Type') (x0 : type1140 a0) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => (x0 (@cons a0 x1 y0)) = (@pair a0 (list a0) x1 y0)) x2.
Definition term16 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : type1654 a0 => @pair a0 (list a0) x0 x1.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : type1394 a0 a1, exists y2 : type1142 a0 a1, ((y2 (@nil a0)) = y0) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = (y1 y3 y4 (y2 y4)))) x0.
Definition term23 (a0 : Type') (x0 : type1140 a0) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : type1654 a0 => @pair a0 (list a0) y2 y3) y0 y1 (x0 y1)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := (fun y0 : type1394 a0 a1 => exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3)))) x1.
Definition term41 (a0 : Type') (x0 : a0) := forall y0 : list a0, forall y1 : a0, forall y2 : list a0, ((@cons a0 x0 y0) = (@cons a0 y1 y2)) = ((x0 = y1) /\ (y0 = y2)).
Definition term32 (a0 : Type') := exists y0 : type1140 a0, forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (@pair a0 (list a0) y1 y2).
Definition term4 (a0 : Type') (x0 : type1140 a0) (x1 : a0) (x2 : list a0) := x0 (@cons a0 x1 x2).
Definition term38 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := (((@cons a0 x0 x1) = (@cons a0 x2 x3)) -> (x0 = x2) /\ (x1 = x3)) /\ (((x0 = x2) /\ (x1 = x3)) -> (@cons a0 x0 x1) = (@cons a0 x2 x3)).
Definition term21 (a0 : Type') (x0 : type1140 a0) (x1 : a0) := fun y0 : list a0 => (x0 (@cons a0 x1 y0)) = (@pair a0 (list a0) x1 y0).
Definition term33 (a0 : Type') := fun y0 : type1140 a0 => forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (@pair a0 (list a0) y1 y2).
Definition term15 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => fun y1 : type1654 a0 => @pair a0 (list a0) x0 y0) x1.
Definition term22 (a0 : Type') (x0 : a0) (x1 : type1140 a0) := forall y0 : list a0, (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : type1654 a0 => @pair a0 (list a0) y1 y2) x0 y0 (x1 y0)).
Definition term20 (a0 : Type') (x0 : a0) (x1 : type1140 a0) := fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : type1654 a0 => @pair a0 (list a0) y1 y2) x0 y0 (x1 y0)).
Definition term19 (a0 : Type') (x0 : type1140 a0) (x1 : a0) (x2 : list a0) := @eq (prod a0 (list a0)) (x0 (@cons a0 x1 x2)).
Definition term24 (a0 : Type') (x0 : type1140 a0) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (@pair a0 (list a0) y0 y1).
Definition term14 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : type1654 a0 => @pair a0 (list a0) y0 y1) x0 x1.
Definition term36 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := ((x0 = x2) /\ (x1 = x3)) -> (@cons a0 x0 x1) = (@cons a0 x2 x3).
Definition term1 (a0 : Type') (x0 : type1140 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (@pair a0 (list a0) y0 y1)) x1.
Definition term18 (a0 : Type') (x0 : a0) (x1 : type1140 a0) (x2 : list a0) := (fun y0 : type1654 a0 => @pair a0 (list a0) x0 x2) (x1 x2).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) (x3 : a1) := (x0 = x1) /\ (x2 = x3).
Definition term30 (a0 : Type') (x0 : type1654 a0) := fun y0 : type1140 a0 => ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (@pair a0 (list a0) y1 y2)).
Definition term29 (a0 : Type') (x0 : type1654 a0) := fun y0 : type1140 a0 => ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : type1654 a0 => @pair a0 (list a0) y3 y4) y1 y2 (y0 y2))).
Definition term11 (a0 : Type') := fun y0 : a0 => fun y1 : list a0 => fun y2 : type1654 a0 => @pair a0 (list a0) y0 y1.
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := forall y0 : list a0, ((@cons a0 x0 x2) = (@cons a0 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term12 (a0 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : type1654 a0 => @pair a0 (list a0) y0 y1) x0.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : type1394 a0 a1, exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3))).
Definition term13 (a0 : Type') (x0 : a0) := fun y0 : list a0 => fun y1 : type1654 a0 => @pair a0 (list a0) x0 y0.
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := ((@cons a0 x0 x2) = (@cons a0 x1 x3)) -> (x0 = x1) /\ (x2 = x3).
Definition term2 (a0 : Type') (x0 : type1140 a0) (x1 : a0) := forall y0 : list a0, (x0 (@cons a0 x1 y0)) = (@pair a0 (list a0) x1 y0).
Definition term17 (a0 : Type') (x0 : a0) (x1 : type1140 a0) (x2 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : type1654 a0 => @pair a0 (list a0) y0 y1) x0 x2 (x1 x2).
Definition term31 (a0 : Type') (x0 : type1654 a0) := exists y0 : type1140 a0, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (@pair a0 (list a0) y1 y2)).
Definition term10 (a0 : Type') (x0 : type1654 a0) := exists y0 : type1140 a0, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : type1654 a0 => @pair a0 (list a0) y3 y4) y1 y2 (y0 y2))).
Definition term9 (a0 : Type') (x0 : type1654 a0) (x1 : type1392 a0) := exists y0 : type1140 a0, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := exists y0 : type1142 a0 a1, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term40 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : a0, forall y1 : list a0, ((@cons a0 x0 x1) = (@cons a0 y0 y1)) = ((x0 = y0) /\ (x1 = y1)).
Definition term25 (a0 : Type') (x0 : type1140 a0) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : type1654 a0 => @pair a0 (list a0) y2 y3) y0 y1 (x0 y1)).
Definition term0 (a0 : Type') (x0 : type1140 a0) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (@pair a0 (list a0) y0 y1).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (x0 = x1) /\ (x2 = x3).
Definition term26 (a0 : Type') (x0 : type1140 a0) (x1 : type1654 a0) := and ((x0 (@nil a0)) = x1).
Definition term28 (a0 : Type') (x0 : type1654 a0) (x1 : type1140 a0) := ((x1 (@nil a0)) = x0) /\ (forall y0 : a0, forall y1 : list a0, (x1 (@cons a0 y0 y1)) = (@pair a0 (list a0) y0 y1)).
Definition term27 (a0 : Type') (x0 : type1654 a0) (x1 : type1140 a0) := ((x1 (@nil a0)) = x0) /\ (forall y0 : a0, forall y1 : list a0, (x1 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : type1654 a0 => @pair a0 (list a0) y2 y3) y0 y1 (x1 y1))).
