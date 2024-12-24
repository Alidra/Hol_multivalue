Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299871 : forall (b : Prop) (x : int) (y : int), ((real_of_int (@COND int b x y)) = (@COND real b (real_of_int x) (real_of_int y))) = ((@COND real b (real_of_int x) (real_of_int y)) = (real_of_int (@COND int b x y))).
