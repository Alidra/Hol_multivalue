Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : real) (x1 : real) := real_add x0 (real_neg x1).
Definition term6 := forall y0 : real, forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1)).
Definition term0 := fun y0 : real => fun y1 : real => real_add y0 (real_neg y1).
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => real_add x0 (real_neg y0)) x1.
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1))) x0.
Definition term5 (x0 : real) := forall y0 : real, (real_sub x0 y0) = (real_add x0 (real_neg y0)).
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub x0 y0) = (real_add x0 (real_neg y0))) x1.
Definition term2 (x0 : real) := fun y0 : real => real_add x0 (real_neg y0).
Definition term1 (x0 : real) := (fun y0 : real => fun y1 : real => real_add y0 (real_neg y1)) x0.
