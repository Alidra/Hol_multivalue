Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5716761 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall op : B -> B -> B, (@support A B op f s) = (@GSPEC A (fun GEN_PVAR_237 : A => exists x : A, @SETSPEC A GEN_PVAR_237 ((@IN A x s) /\ (~ ((f x) = (@neutral B op)))) x)).
