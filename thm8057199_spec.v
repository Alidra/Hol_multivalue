Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8057199 : forall {_143007 _143008 _143009 : Type'}, forall s : (cart _143007 _143008) -> Prop, forall f : ((cart _143007 _143009) -> Prop) -> Prop, (@PCROSS _143007 _143008 _143009 s (@INTERS (cart _143007 _143009) f)) = (@COND ((cart _143007 (finite_sum _143008 _143009)) -> Prop) (f = (@EMPTY ((cart _143007 _143009) -> Prop))) (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009))) (@INTERS (cart _143007 (finite_sum _143008 _143009)) (@GSPEC ((cart _143007 (finite_sum _143008 _143009)) -> Prop) (fun GEN_PVAR_368 : (cart _143007 (finite_sum _143008 _143009)) -> Prop => exists t : (cart _143007 _143009) -> Prop, @SETSPEC ((cart _143007 (finite_sum _143008 _143009)) -> Prop) GEN_PVAR_368 (@IN ((cart _143007 _143009) -> Prop) t f) (@PCROSS _143007 _143008 _143009 s t))))).
