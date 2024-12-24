Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8057341 : forall {A M N : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N) -> Prop, forall s' : (cart A M) -> Prop, forall t' : (cart A N) -> Prop, (@DISJOINT (cart A (finite_sum M N)) (@PCROSS A M N s t) (@PCROSS A M N s' t')) = ((@DISJOINT (cart A M) s s') \/ (@DISJOINT (cart A N) t t')).
