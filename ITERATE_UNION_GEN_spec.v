Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5764561 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@FINITE A (@support A B op f s)) /\ ((@FINITE A (@support A B op f t)) /\ (@DISJOINT A (@support A B op f s) (@support A B op f t)))) -> (@iterate B A op (@UNION A s t) f) = (op (@iterate B A op s f) (@iterate B A op t f)).
