Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') := fun y0 : type1413 a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2).
Definition term1 (a0 : Type') (a1 : Type') := fun y0 : type475 a0 a1 => y0 (@ε (a0 -> a1 -> Prop) y0).
Definition term0 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term3 (a0 : Type') (a1 : Type') := exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2).
Definition term4 (a0 : Type') (a1 : Type') := (fun y0 : type475 a0 a1 => y0 (@ε (a0 -> a1 -> Prop) y0)) (fun y0 : type1413 a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2)).
Definition term5 (a0 : Type') (a1 : Type') := (fun y0 : type1413 a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2)) (@ε (a0 -> a1 -> Prop) (fun y0 : type1413 a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))).
