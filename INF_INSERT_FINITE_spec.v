Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5256773 : forall x : real, forall s : real -> Prop, (@FINITE real s) -> (inf (@INSERT real x s)) = (@COND real (s = (@EMPTY real)) x (real_min x (inf s))).
