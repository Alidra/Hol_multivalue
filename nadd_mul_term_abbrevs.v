Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_mul y0 y1) = (mk_nadd (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2)))) x0.
Definition term0 := fun y0 : nadd => fun y1 : nadd => mk_nadd (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2)).
Definition term6 := forall y0 : nadd, forall y1 : nadd, (nadd_mul y0 y1) = (mk_nadd (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2))).
Definition term1 (x0 : nadd) := (fun y0 : nadd => fun y1 : nadd => mk_nadd (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2))) x0.
Definition term8 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_mul x0 y0) = (mk_nadd (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1)))) x1.
Definition term4 (x0 : nadd) (x1 : nadd) := mk_nadd (fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)).
Definition term5 (x0 : nadd) := forall y0 : nadd, (nadd_mul x0 y0) = (mk_nadd (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1))).
Definition term3 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => mk_nadd (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1))) x1.
Definition term2 (x0 : nadd) := fun y0 : nadd => mk_nadd (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1)).
