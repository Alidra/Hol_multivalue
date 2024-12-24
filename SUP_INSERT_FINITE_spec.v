Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5178187 : forall x : real, forall s : real -> Prop, (@FINITE real s) -> (sup (@INSERT real x s)) = (@COND real (s = (@EMPTY real)) x (real_max x (sup s))).
