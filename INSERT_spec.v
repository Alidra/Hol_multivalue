Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3192218 : forall {A : Type'} (s : A -> Prop) (x : A), (@INSERT A x s) = (@GSPEC A (fun GEN_PVAR_5 : A => exists y : A, @SETSPEC A GEN_PVAR_5 ((@IN A y s) \/ (y = x)) y)).
