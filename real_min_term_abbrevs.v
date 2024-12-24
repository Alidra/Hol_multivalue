Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := fun y0 : real => fun y1 : real => @COND real (real_le y0 y1) y0 y1.
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => @COND real (real_le x0 y0) x0 y0) x1.
Definition term6 := forall y0 : real, forall y1 : real, (real_min y0 y1) = (@COND real (real_le y0 y1) y0 y1).
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => (real_min x0 y0) = (@COND real (real_le x0 y0) x0 y0)) x1.
Definition term2 (x0 : real) := fun y0 : real => @COND real (real_le x0 y0) x0 y0.
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, (real_min y0 y1) = (@COND real (real_le y0 y1) y0 y1)) x0.
Definition term1 (x0 : real) := (fun y0 : real => fun y1 : real => @COND real (real_le y0 y1) y0 y1) x0.
Definition term5 (x0 : real) := forall y0 : real, (real_min x0 y0) = (@COND real (real_le x0 y0) x0 y0).
Definition term4 (x0 : real) (x1 : real) := @COND real (real_le x0 x1) x0 x1.
