Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ((rem x0 y0) = (rem x1 y0)) = (@eq2 int x0 x1 (int_mod y0))) x2.
Definition term1 (x0 : int) (x1 : int) (x2 : int) := @eq2 int x0 x1 (int_mod x2).
