Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3754706 : forall {A : Type'}, forall f : (A -> Prop) -> Prop, (@FINITE (A -> Prop) f) -> (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_104 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_104 ((@IN (A -> Prop) t f) /\ (forall u : A -> Prop, (@IN (A -> Prop) u f) -> ~ (@PSUBSET A t u))) t))) = (@UNIONS A f).
