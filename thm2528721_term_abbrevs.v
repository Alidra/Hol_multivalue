Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) (x1 : int) := forall y0 : int, ((rem x0 y0) = (rem x1 y0)) = (@eq2 int x0 x1 (int_mod y0)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, ((rem x0 y1) = (rem y0 y1)) = (@eq2 int x0 y0 (int_mod y1))) x1.
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ((rem x0 y0) = (rem x1 y0)) = (@eq2 int x0 x1 (int_mod y0))) x2.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((rem y0 y2) = (rem y1 y2)) = (@eq2 int y0 y1 (int_mod y2))) x0.
Definition term1 (x0 : int) := forall y0 : int, forall y1 : int, ((rem x0 y1) = (rem y0 y1)) = (@eq2 int x0 y0 (int_mod y1)).
