Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (a0 : Type') := forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1).
Definition term0 (a0 : Type') (x0 : type1351 a0) := (fun y0 : type1351 a0 => (forall y1 : type6 a0, y0 (@mktybit1 a0 y1)) -> forall y1 : tybit1 a0, y0 y1) x0.
Definition term26 (a0 : Type') (x0 : type6 a0) := forall y0 : type6 a0, (y0 = x0) -> (fun y1 : type6 a0 => (@mktybit1 a0 x0) = (@mktybit1 a0 y1)) y0.
Definition term18 (a0 : Type') (x0 : type6 a0) (x1 : type6 a0) := (fun y0 : type6 a0 => (@mktybit1 a0 x0) = (@mktybit1 a0 y0)) x1.
Definition term17 (a0 : Type') := (forall y0 : type6 a0, exists y1 : type6 a0, (@mktybit1 a0 y0) = (@mktybit1 a0 y1)) -> forall y0 : tybit1 a0, exists y1 : type6 a0, y0 = (@mktybit1 a0 y1).
Definition term5 (a0 : Type') (x0 : type6 a0) := exists y0 : type6 a0, (@mktybit1 a0 x0) = (@mktybit1 a0 y0).
Definition term8 (a0 : Type') := forall y0 : type6 a0, (fun y1 : tybit1 a0 => exists y2 : type6 a0, y1 = (@mktybit1 a0 y2)) (@mktybit1 a0 y0).
Definition term25 (a0 : Type') (x0 : type6 a0) (x1 : type6 a0) := (x1 = x0) -> (fun y0 : type6 a0 => (@mktybit1 a0 x0) = (@mktybit1 a0 y0)) x1.
Definition term15 (a0 : Type') := forall y0 : tybit1 a0, (fun y1 : tybit1 a0 => exists y2 : type6 a0, y1 = (@mktybit1 a0 y2)) y0.
Definition term22 (a0 : Type') (x0 : type6 a0) := forall y0 : type6 a0, (forall y1 : type6 a0, (y1 = y0) -> (fun y2 : type6 a0 => (@mktybit1 a0 x0) = (@mktybit1 a0 y2)) y1) -> exists y1 : type6 a0, (@mktybit1 a0 x0) = (@mktybit1 a0 y1).
Definition term21 (a0 : Type') (x0 : type6 a0) := fun y0 : type6 a0 => (@mktybit1 a0 x0) = (@mktybit1 a0 y0).
Definition term1 (a0 : Type') (x0 : type1351 a0) := (forall y0 : type6 a0, x0 (@mktybit1 a0 y0)) -> forall y0 : tybit1 a0, x0 y0.
Definition term24 (a0 : Type') (x0 : type6 a0) := (forall y0 : type6 a0, (y0 = x0) -> (fun y1 : type6 a0 => (@mktybit1 a0 x0) = (@mktybit1 a0 y1)) y0) -> exists y0 : type6 a0, (@mktybit1 a0 x0) = (@mktybit1 a0 y0).
Definition term13 (a0 : Type') (x0 : tybit1 a0) := exists y0 : type6 a0, x0 = (@mktybit1 a0 y0).
Definition term6 (a0 : Type') := fun y0 : type6 a0 => (fun y1 : tybit1 a0 => exists y2 : type6 a0, y1 = (@mktybit1 a0 y2)) (@mktybit1 a0 y0).
Definition term14 (a0 : Type') := fun y0 : tybit1 a0 => (fun y1 : tybit1 a0 => exists y2 : type6 a0, y1 = (@mktybit1 a0 y2)) y0.
Definition term7 (a0 : Type') := fun y0 : type6 a0 => exists y1 : type6 a0, (@mktybit1 a0 y0) = (@mktybit1 a0 y1).
Definition term20 (a0 : Type') (x0 : type6 a0) := (fun y0 : type42 a0 => forall y1 : type6 a0, (forall y2 : type6 a0, (y2 = y1) -> y0 y2) -> ex y0) (fun y0 : type6 a0 => (@mktybit1 a0 x0) = (@mktybit1 a0 y0)).
Definition term10 (a0 : Type') := imp (forall y0 : type6 a0, (fun y1 : tybit1 a0 => exists y2 : type6 a0, y1 = (@mktybit1 a0 y2)) (@mktybit1 a0 y0)).
Definition term19 (a0 : Type') := forall y0 : type42 a0, forall y1 : type6 a0, (forall y2 : type6 a0, (y2 = y1) -> y0 y2) -> ex y0.
Definition term4 (a0 : Type') (x0 : type6 a0) := (fun y0 : tybit1 a0 => exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) (@mktybit1 a0 x0).
Definition term12 (a0 : Type') (x0 : tybit1 a0) := (fun y0 : tybit1 a0 => exists y1 : type6 a0, y0 = (@mktybit1 a0 y1)) x0.
Definition term2 (a0 : Type') := (forall y0 : type6 a0, (fun y1 : tybit1 a0 => exists y2 : type6 a0, y1 = (@mktybit1 a0 y2)) (@mktybit1 a0 y0)) -> forall y0 : tybit1 a0, (fun y1 : tybit1 a0 => exists y2 : type6 a0, y1 = (@mktybit1 a0 y2)) y0.
Definition term23 (a0 : Type') (x0 : type6 a0) := (fun y0 : type6 a0 => (forall y1 : type6 a0, (y1 = y0) -> (fun y2 : type6 a0 => (@mktybit1 a0 x0) = (@mktybit1 a0 y2)) y1) -> exists y1 : type6 a0, (@mktybit1 a0 x0) = (@mktybit1 a0 y1)) x0.
Definition term3 (a0 : Type') := fun y0 : tybit1 a0 => exists y1 : type6 a0, y0 = (@mktybit1 a0 y1).
Definition term11 (a0 : Type') := imp (forall y0 : type6 a0, exists y1 : type6 a0, (@mktybit1 a0 y0) = (@mktybit1 a0 y1)).
Definition term9 (a0 : Type') := forall y0 : type6 a0, exists y1 : type6 a0, (@mktybit1 a0 y0) = (@mktybit1 a0 y1).
