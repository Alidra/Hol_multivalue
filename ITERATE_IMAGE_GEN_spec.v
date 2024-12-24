Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6158399 : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall f : A -> B, forall g : A -> C, forall s : A -> Prop, (@FINITE A s) -> (@iterate C A op s g) = (@iterate C B op (@IMAGE A B f s) (fun y : B => @iterate C A op (@GSPEC A (fun GEN_PVAR_245 : A => exists x : A, @SETSPEC A GEN_PVAR_245 ((@IN A x s) /\ ((f x) = y)) x)) g)).
