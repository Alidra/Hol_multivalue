Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3193179 : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@DELETE A s x) = (@GSPEC A (fun GEN_PVAR_6 : A => exists y : A, @SETSPEC A GEN_PVAR_6 ((@IN A y s) /\ (~ (y = x))) y)).
