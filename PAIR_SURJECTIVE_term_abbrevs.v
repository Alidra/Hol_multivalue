Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) (x2 : a1) := imp ((@ABS_prod a0 a1 (@REP_prod a0 a1 x0)) = (@ABS_prod a0 a1 (@mk_pair a0 a1 x1 x2))).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := exists y0 : a1, (@ABS_prod a0 a1 (@mk_pair a0 a1 x1 x0)) = (@ABS_prod a0 a1 (@mk_pair a0 a1 x1 y0)).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y1 y2))) (@ABS_prod a0 a1 (@mk_pair a0 a1 x0 x1)).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := exists y0 : a0, exists y1 : a1, (@ABS_prod a0 a1 (@mk_pair a0 a1 x0 x1)) = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := exists y0 : a0, exists y1 : a1, x0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := exists y0 : a0, exists y1 : a1, x0 = (@pair a0 a1 y0 y1).
Definition term5 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := exists y0 : a0, exists y1 : a1, (@REP_prod a0 a1 x0) = (@mk_pair a0 a1 y0 y1).
Definition term32 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y1 y2)).
Definition term24 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := ((exists y0 : a0, exists y1 : a1, (@REP_prod a0 a1 x0) = (@mk_pair a0 a1 y0 y1)) = ((@REP_prod a0 a1 (@ABS_prod a0 a1 (@REP_prod a0 a1 x0))) = (@REP_prod a0 a1 x0))) -> exists y0 : a0, exists y1 : a1, x0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := fun y0 : a1 => x0 = (@pair a0 a1 x1 y0).
Definition term33 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y1 y2))) x0.
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : prod a0 a1) := ((@ABS_prod a0 a1 (@REP_prod a0 a1 x2)) = (@ABS_prod a0 a1 (@mk_pair a0 a1 x0 x1))) -> exists y0 : a0, exists y1 : a1, x2 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1)).
Definition term42 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := fun y0 : a1 => (@REP_prod a0 a1 x0) = (@mk_pair a0 a1 x1 y0).
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, (@ABS_prod a0 a1 (@REP_prod a0 a1 y0)) = y0.
Definition term13 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := exists y0 : a1, x0 = (@pair a0 a1 x1 y0).
Definition term26 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := exists y0 : a1, (@REP_prod a0 a1 x0) = (@mk_pair a0 a1 x1 y0).
Definition term3 (a0 : Type') (a1 : Type') := forall y0 : type1413 a0 a1, (exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2)) = ((@REP_prod a0 a1 (@ABS_prod a0 a1 y0)) = y0).
Definition term12 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := fun y0 : a1 => x0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 x1 y0)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (exists y0 : a0, exists y1 : a1, (@REP_prod a0 a1 x0) = (@mk_pair a0 a1 y0 y1)) -> exists y0 : a0, exists y1 : a1, x0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := fun y0 : a0 => exists y1 : a1, x0 = (@pair a0 a1 y0 y1).
Definition term22 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := imp ((exists y0 : a0, exists y1 : a1, (@REP_prod a0 a1 x0) = (@mk_pair a0 a1 y0 y1)) = ((@REP_prod a0 a1 (@ABS_prod a0 a1 (@REP_prod a0 a1 x0))) = (@REP_prod a0 a1 x0))).
Definition term20 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @eq (a0 -> a1 -> Prop) (@REP_prod a0 a1 x0).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@pair a0 a1 x0 y0) = (@ABS_prod a0 a1 (@mk_pair a0 a1 x0 y0))) x1.
Definition term43 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := fun y0 : a0 => exists y1 : a1, (@REP_prod a0 a1 x0) = (@mk_pair a0 a1 y0 y1).
Definition term19 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @eq (a0 -> a1 -> Prop) (@REP_prod a0 a1 (@ABS_prod a0 a1 (@REP_prod a0 a1 x0))).
Definition term4 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : type1413 a0 a1 => (exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2)) = ((@REP_prod a0 a1 (@ABS_prod a0 a1 y0)) = y0)) (@REP_prod a0 a1 x0).
Definition term14 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := exists y0 : a1, x0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 x1 y0)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @REP_prod a0 a1 (@ABS_prod a0 a1 (@REP_prod a0 a1 x0)).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := fun y0 : a0 => exists y1 : a1, (@ABS_prod a0 a1 (@mk_pair a0 a1 x0 x1)) = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1)).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : prod a0 a1) := (x2 = (@ABS_prod a0 a1 (@mk_pair a0 a1 x0 x1))) -> exists y0 : a0, exists y1 : a1, x2 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1)).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @ABS_prod a0 a1 (@mk_pair a0 a1 x0 x1).
Definition term23 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := imp (exists y0 : a0, exists y1 : a1, (@REP_prod a0 a1 x0) = (@mk_pair a0 a1 y0 y1)).
Definition term44 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@pair a0 a1 y1 y2).
Definition term2 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @ABS_prod a0 a1 (@REP_prod a0 a1 x0).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@pair a0 a1 y0 y1) = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1))) x0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : prod a0 a1 => (@ABS_prod a0 a1 (@REP_prod a0 a1 y0)) = y0) x0.
Definition term16 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := fun y0 : a0 => exists y1 : a1, x0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1)).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := fun y0 : a1 => (@ABS_prod a0 a1 (@mk_pair a0 a1 x1 x0)) = (@ABS_prod a0 a1 (@mk_pair a0 a1 x1 y0)).
Definition term37 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @eq Prop (exists y0 : a0, exists y1 : a1, x0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1))).
Definition term21 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @eq Prop (exists y0 : a0, exists y1 : a1, (@REP_prod a0 a1 x0) = (@mk_pair a0 a1 y0 y1)).
Definition term27 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @eq (prod a0 a1) (@ABS_prod a0 a1 (@REP_prod a0 a1 x0)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @eq Prop ((fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y1 y2))) x0).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : prod a0 a1) := ((@REP_prod a0 a1 x2) = (@mk_pair a0 a1 x0 x1)) -> exists y0 : a0, exists y1 : a1, x2 = (@ABS_prod a0 a1 (@mk_pair a0 a1 y0 y1)).
Definition term29 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) (x2 : a1) := imp (x0 = (@ABS_prod a0 a1 (@mk_pair a0 a1 x1 x2))).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@pair a0 a1 x0 y0) = (@ABS_prod a0 a1 (@mk_pair a0 a1 x0 y0)).
