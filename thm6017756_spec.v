Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6017756 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, (@SUBSET A (@support A B op f (@UNIV A)) s) -> (@iterate B A op s f) = (@iterate B A op (@UNIV A) f).
