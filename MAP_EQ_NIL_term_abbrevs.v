Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => ~ ((@cons a0 x0 y0) = (@nil a0))) x1.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, forall y2 : list a0, (@List.map a0 a1 y0 (@cons a0 y1 y2)) = (@cons a1 (y0 y1) (@List.map a0 a1 y0 y2))) x0.
Definition term42 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := forall y0 : list a1, ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1)).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) := forall y0 : list a1, (((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) -> ((@List.map a1 a0 x0 (@cons a1 x1 y0)) = (@nil a0)) = ((@cons a1 x1 y0) = (@nil a1)).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : list a1) := imp ((fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) x1).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := and ((fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) (@nil a1)).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := fun y0 : a1 => forall y1 : list a1, (((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) -> ((@List.map a1 a0 x0 (@cons a1 y0 y1)) = (@nil a0)) = ((@cons a1 y0 y1) = (@nil a1)).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : list a0) := (fun y0 : list a0 => (@List.map a0 a1 x1 (@cons a0 x0 y0)) = (@cons a1 (x1 x0) (@List.map a0 a1 x1 y0))) x2.
Definition term38 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := imp (((fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) (@nil a1)) /\ (forall y0 : a1, forall y1 : list a1, ((fun y2 : list a1 => ((@List.map a1 a0 x0 y2) = (@nil a0)) = (y2 = (@nil a1))) y1) -> (fun y2 : list a1 => ((@List.map a1 a0 x0 y2) = (@nil a0)) = (y2 = (@nil a1))) (@cons a1 y0 y1))).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := (((fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) (@nil a1)) /\ (forall y0 : a1, forall y1 : list a1, ((fun y2 : list a1 => ((@List.map a1 a0 x0 y2) = (@nil a0)) = (y2 = (@nil a1))) y1) -> (fun y2 : list a1 => ((@List.map a1 a0 x0 y2) = (@nil a0)) = (y2 = (@nil a1))) (@cons a1 y0 y1))) -> forall y0 : list a1, (fun y1 : list a1 => ((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) y0.
Definition term15 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : list a0, ~ ((@cons a0 x0 y0) = (@nil a0)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := (fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) (@nil a1).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := fun y0 : list a1 => (fun y1 : list a1 => ((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) y0.
Definition term46 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> a0) (x2 : list a1) := @cons a0 (x1 x0) (@List.map a1 a0 x1 x2).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => forall y1 : list a0, (@List.map a0 a1 x0 (@cons a0 y0 y1)) = (@cons a1 (x0 y0) (@List.map a0 a1 x0 y1))) x1.
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, ~ ((@cons a0 y0 y1) = (@nil a0))) x0.
Definition term45 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := @eq Prop ((@List.map a1 a0 x0 (@nil a1)) = (@nil a0)).
Definition term43 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := ((((@List.map a1 a0 x0 (@nil a1)) = (@nil a0)) = ((@nil a1) = (@nil a1))) /\ (forall y0 : a1, forall y1 : list a1, (((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) -> ((@List.map a1 a0 x0 (@cons a1 y0 y1)) = (@nil a0)) = ((@cons a1 y0 y1) = (@nil a1)))) -> forall y0 : list a1, ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := @eq (list a0) (@List.map a1 a0 x0 (@nil a1)).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := imp ((((@List.map a1 a0 x0 (@nil a1)) = (@nil a0)) = ((@nil a1) = (@nil a1))) /\ (forall y0 : a1, forall y1 : list a1, (((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) -> ((@List.map a1 a0 x0 (@cons a1 y0 y1)) = (@nil a0)) = ((@cons a1 y0 y1) = (@nil a1)))).
Definition term27 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : list a1) := (((@List.map a1 a0 x0 x2) = (@nil a0)) = (x2 = (@nil a1))) -> ((@List.map a1 a0 x0 (@cons a1 x1 x2)) = (@nil a0)) = ((@cons a1 x1 x2) = (@nil a1)).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : list a1) := imp (((@List.map a1 a0 x0 x1) = (@nil a0)) = (x1 = (@nil a1))).
Definition term49 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : list a1) := @eq Prop ((@List.map a1 a0 x0 (@cons a1 x1 x2)) = (@nil a0)).
Definition term4 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ ((@cons a0 x0 x1) = (@nil a0))) -> ((@cons a0 x0 x1) = (@nil a0)) = False.
Definition term20 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := and (((@List.map a1 a0 x0 (@nil a1)) = (@nil a0)) = ((@nil a1) = (@nil a1))).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (@List.map a0 a1 y0 (@nil a0)) = (@nil a1)) x0.
Definition term30 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) := forall y0 : list a1, ((fun y1 : list a1 => ((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) y0) -> (fun y1 : list a1 => ((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) (@cons a1 x1 y0).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : list a1) := @List.map a1 a0 x0 (@cons a1 x1 x2).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := forall y0 : a1, forall y1 : list a1, (((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) -> ((@List.map a1 a0 x0 (@cons a1 y0 y1)) = (@nil a0)) = ((@cons a1 y0 y1) = (@nil a1)).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := forall y0 : a1, forall y1 : list a1, ((fun y2 : list a1 => ((@List.map a1 a0 x0 y2) = (@nil a0)) = (y2 = (@nil a1))) y1) -> (fun y2 : list a1 => ((@List.map a1 a0 x0 y2) = (@nil a0)) = (y2 = (@nil a1))) (@cons a1 y0 y1).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : list a0) := @cons a1 (x1 x0) (@List.map a0 a1 x1 x2).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := ((fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) (@nil a1)) /\ (forall y0 : a1, forall y1 : list a1, ((fun y2 : list a1 => ((@List.map a1 a0 x0 y2) = (@nil a0)) = (y2 = (@nil a1))) y1) -> (fun y2 : list a1 => ((@List.map a1 a0 x0 y2) = (@nil a0)) = (y2 = (@nil a1))) (@cons a1 y0 y1)).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : list a1) := ((fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) x2) -> (fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) (@cons a1 x1 x2).
Definition term13 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, (@List.map a0 a1 y0 (@nil a0)) = (@nil a1).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1)).
Definition term50 (a0 : Type') (a1 : Type') := forall y0 : a1 -> a0, forall y1 : list a1, ((@List.map a1 a0 y0 y1) = (@nil a0)) = (y1 = (@nil a1)).
Definition term3 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ ((@cons a0 x0 x1) = (@nil a0)).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : list a1) := (fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) (@cons a1 x1 x2).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) := forall y0 : list a0, (@List.map a0 a1 x1 (@cons a0 x0 y0)) = (@cons a1 (x1 x0) (@List.map a0 a1 x1 y0)).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : list a1) := @eq (list a0) (@List.map a1 a0 x0 (@cons a1 x1 x2)).
Definition term29 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) := fun y0 : list a1 => (((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) -> ((@List.map a1 a0 x0 (@cons a1 x1 y0)) = (@nil a0)) = ((@cons a1 x1 y0) = (@nil a1)).
Definition term48 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> a0) (x2 : list a1) := @eq (list a0) (@cons a0 (x1 x0) (@List.map a1 a0 x1 x2)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : list a0) := @List.map a0 a1 x0 (@cons a0 x1 x2).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) := fun y0 : list a1 => ((fun y1 : list a1 => ((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) y0) -> (fun y1 : list a1 => ((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) (@cons a1 x1 y0).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := (((@List.map a1 a0 x0 (@nil a1)) = (@nil a0)) = ((@nil a1) = (@nil a1))) /\ (forall y0 : a1, forall y1 : list a1, (((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) -> ((@List.map a1 a0 x0 (@cons a1 y0 y1)) = (@nil a0)) = ((@cons a1 y0 y1) = (@nil a1))).
Definition term5 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0, forall y2 : list a0, (@List.map a0 a1 y0 (@cons a0 y1 y2)) = (@cons a1 (y0 y1) (@List.map a0 a1 y0 y2)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : list a1) := (fun y0 : list a1 => ((@List.map a1 a0 x0 y0) = (@nil a0)) = (y0 = (@nil a1))) x1.
Definition term32 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := fun y0 : a1 => forall y1 : list a1, ((fun y2 : list a1 => ((@List.map a1 a0 x0 y2) = (@nil a0)) = (y2 = (@nil a1))) y1) -> (fun y2 : list a1 => ((@List.map a1 a0 x0 y2) = (@nil a0)) = (y2 = (@nil a1))) (@cons a1 y0 y1).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := forall y0 : list a1, (fun y1 : list a1 => ((@List.map a1 a0 x0 y1) = (@nil a0)) = (y1 = (@nil a1))) y0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, forall y1 : list a0, (@List.map a0 a1 x0 (@cons a0 y0 y1)) = (@cons a1 (x0 y0) (@List.map a0 a1 x0 y1)).