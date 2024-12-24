Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5773307 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@FINITE A (@support A B op f s)) /\ (@SUBSET A (@support A B op f t) (@support A B op f s))) -> (op (@iterate B A op (@DIFF A s t) f) (@iterate B A op t f)) = (@iterate B A op s f).
