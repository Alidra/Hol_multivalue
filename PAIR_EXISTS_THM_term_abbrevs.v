Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term32 (a0 : Type') (a1 : Type') (x0 : type475 a0 a1) := forall y0 : type1413 a0 a1, ~ (x0 y0).
Definition term47 := (~ False) -> False.
Definition term19 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a1) := ~ ((fun y0 : a1 => x0 = (@mk_pair a0 a1 x1 y0)) x2).
Definition term8 (x0 : Prop) := ~ (~ x0).
Definition term40 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := (fun y0 : a0 => forall y1 : a1, ~ (x0 = (@mk_pair a0 a1 y0 y1))) x1.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := fun y0 : a1 => x0 = (@mk_pair a0 a1 x1 y0).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term23 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := forall y0 : a1, ~ (x0 = (@mk_pair a0 a1 x1 y0)).
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := ~ (exists y0 : a0, exists y1 : a1, x0 = (@mk_pair a0 a1 y0 y1)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0, exists y1 : a1, x0 = (@mk_pair a0 a1 y0 y1).
Definition term34 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2)) x0.
Definition term41 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a1) := (fun y0 : a1 => ~ (x0 = (@mk_pair a0 a1 x1 y0))) x2.
Definition term46 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := ((@mk_pair a0 a1 x0 x1) = (@mk_pair a0 a1 x0 x1)) -> False.
Definition term43 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := ~ ((@mk_pair a0 a1 x0 x1) = (@mk_pair a0 a1 x0 x1)).
Definition term44 (x0 : Prop) := (~ x0) -> x0.
Definition term35 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := ~ ((fun y0 : type1413 a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2)) x0).
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := fun y0 : a1 => ~ (x0 = (@mk_pair a0 a1 x1 y0)).
Definition term13 (a0 : Type') (a1 : Type') := fun y0 : type1413 a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2).
Definition term2 (a0 : Type') (a1 : Type') := (~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))) -> False.
Definition term45 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a1) := (x0 = (@mk_pair a0 a1 x1 x2)) -> False.
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := exists y0 : a1, x0 = (@mk_pair a0 a1 x1 y0).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a1) := (fun y0 : a1 => x0 = (@mk_pair a0 a1 x1 y0)) x2.
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := fun y0 : a0 => exists y1 : a1, x0 = (@mk_pair a0 a1 y0 y1).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term4 (a0 : Type') (a1 : Type') := ((~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))) -> False) -> (~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))) -> False.
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := fun y0 : a0 => ~ ((fun y1 : a0 => exists y2 : a1, x0 = (@mk_pair a0 a1 y1 y2)) y0).
Definition term33 (a0 : Type') (a1 : Type') := forall y0 : type1413 a0 a1, ~ ((fun y1 : type1413 a0 a1 => exists y2 : a0, exists y3 : a1, y1 = (@mk_pair a0 a1 y2 y3)) y0).
Definition term37 (a0 : Type') (a1 : Type') := fun y0 : type1413 a0 a1 => forall y1 : a0, forall y2 : a1, ~ (y0 = (@mk_pair a0 a1 y1 y2)).
Definition term31 (a0 : Type') (a1 : Type') (x0 : type475 a0 a1) := ~ (ex x0).
Definition term30 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, forall y1 : a1, ~ (x0 = (@mk_pair a0 a1 y0 y1)).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := ~ ((fun y0 : a0 => exists y1 : a1, x0 = (@mk_pair a0 a1 y0 y1)) x1).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (~ ((@mk_pair a0 a1 x0 x1) = (@mk_pair a0 a1 x0 x1))) -> (@mk_pair a0 a1 x0 x1) = (@mk_pair a0 a1 x0 x1).
Definition term5 (a0 : Type') (a1 : Type') := (((~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))) -> False) -> (~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))) -> False) -> (~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))) -> False.
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := ~ (exists y0 : a1, x0 = (@mk_pair a0 a1 x1 y0)).
Definition term1 (a0 : Type') (a1 : Type') := exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := (fun y0 : a0 => exists y1 : a1, x0 = (@mk_pair a0 a1 y0 y1)) x1.
Definition term38 (a0 : Type') (a1 : Type') := forall y0 : type1413 a0 a1, forall y1 : a0, forall y2 : a1, ~ (y0 = (@mk_pair a0 a1 y1 y2)).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a1) := ~ (x0 = (@mk_pair a0 a1 x1 x2)).
Definition term39 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => forall y1 : a0, forall y2 : a1, ~ (y0 = (@mk_pair a0 a1 y1 y2))) x0.
Definition term6 (a0 : Type') (a1 : Type') := (((~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))) -> False) -> (~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))) -> False) -> ((~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))) -> False) -> (~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))) -> False.
Definition term17 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := forall y0 : a1, ~ ((fun y1 : a1 => x0 = (@mk_pair a0 a1 x1 y1)) y0).
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := fun y0 : a1 => ~ ((fun y1 : a1 => x0 = (@mk_pair a0 a1 x1 y1)) y0).
Definition term7 (a0 : Type') (a1 : Type') := ~ (~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2))).
Definition term36 (a0 : Type') (a1 : Type') := fun y0 : type1413 a0 a1 => ~ ((fun y1 : type1413 a0 a1 => exists y2 : a0, exists y3 : a1, y1 = (@mk_pair a0 a1 y2 y3)) y0).
Definition term25 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, ~ ((fun y1 : a0 => exists y2 : a1, x0 = (@mk_pair a0 a1 y1 y2)) y0).
Definition term3 (a0 : Type') (a1 : Type') := ~ (exists y0 : type1413 a0 a1, exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2)).
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := fun y0 : a0 => forall y1 : a1, ~ (x0 = (@mk_pair a0 a1 y0 y1)).