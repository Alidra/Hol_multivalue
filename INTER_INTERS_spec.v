Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3483752 : forall {A : Type'}, (forall f : (A -> Prop) -> Prop, forall s : A -> Prop, (@INTER A s (@INTERS A f)) = (@COND (A -> Prop) (f = (@EMPTY (A -> Prop))) s (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_75 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_75 (@IN (A -> Prop) t f) (@INTER A s t)))))) /\ (forall f : (A -> Prop) -> Prop, forall s : A -> Prop, (@INTER A (@INTERS A f) s) = (@COND (A -> Prop) (f = (@EMPTY (A -> Prop))) s (@INTERS A (@GSPEC (A -> Prop) (fun GEN_PVAR_76 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_76 (@IN (A -> Prop) t f) (@INTER A t s)))))).
