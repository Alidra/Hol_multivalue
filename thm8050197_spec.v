Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8050197 : forall {_143007 _143008 _143009 : Type'} (s : (cart _143007 _143008) -> Prop) (f : ((cart _143007 _143009) -> Prop) -> Prop) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))), (forall x : cart _143007 _143008, forall y : cart _143007 _143009, ((@IN (cart _143007 _143008) x s) /\ (@IN (cart _143007 _143009) y (@INTERS (cart _143007 _143009) (@EMPTY ((cart _143007 _143009) -> Prop))))) = ((@IN (cart _143007 _143008) x s) /\ (@IN (cart _143007 _143009) y (@UNIV (cart _143007 _143009))))) = ((@PCROSS _143007 _143008 _143009 s (@INTERS (cart _143007 _143009) f)) = (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009)))).
