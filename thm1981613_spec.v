Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1981613 : forall (x1 : real) (x2 : real) (y1 : real) (y2 : real), (real_mul (real_div x1 y1) (real_div x2 y2)) = (real_div (real_mul x1 x2) (real_mul y1 y2)).
