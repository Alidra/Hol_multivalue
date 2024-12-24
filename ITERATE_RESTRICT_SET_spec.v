Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5986609 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall P : A -> Prop, forall s : A -> Prop, forall f : A -> B, (@iterate B A op (@GSPEC A (fun GEN_PVAR_242 : A => exists x : A, @SETSPEC A GEN_PVAR_242 ((@IN A x s) /\ (P x)) x)) f) = (@iterate B A op s (fun x : A => @COND B (P x) (f x) (@neutral B op))).
