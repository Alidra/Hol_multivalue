Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3556963 : forall {A B : Type'}, forall f : A -> B, forall g : (A -> Prop) -> Prop, forall s : A -> Prop, ((~ (g = (@EMPTY (A -> Prop)))) /\ (forall t : A -> Prop, (@IN (A -> Prop) t (@DELETE (A -> Prop) g s)) -> @SUBSET A (@GSPEC A (fun GEN_PVAR_88 : A => exists x : A, @SETSPEC A GEN_PVAR_88 (@IN B (f x) (@IMAGE A B f t)) x)) t)) -> (@IMAGE A B f (@INTERS A g)) = (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) g)).
