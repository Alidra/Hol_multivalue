Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1))) x0.
