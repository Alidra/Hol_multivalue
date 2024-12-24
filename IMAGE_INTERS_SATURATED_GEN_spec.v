Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3552877 : forall {A B : Type'}, forall f : A -> B, forall g : (A -> Prop) -> Prop, forall s : A -> Prop, forall u : A -> Prop, ((~ (g = (@EMPTY (A -> Prop)))) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t g) -> @SUBSET A t u) /\ (forall t : A -> Prop, (@IN (A -> Prop) t (@DELETE (A -> Prop) g s)) -> @SUBSET A (@GSPEC A (fun GEN_PVAR_85 : A => exists x : A, @SETSPEC A GEN_PVAR_85 ((@IN A x u) /\ (@IN B (f x) (@IMAGE A B f t))) x)) t))) -> (@IMAGE A B f (@INTERS A g)) = (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) g)).
