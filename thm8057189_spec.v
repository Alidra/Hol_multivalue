Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8057189 : forall {_143061 _143062 _143063 : Type'}, forall f : ((cart _143061 _143062) -> Prop) -> Prop, forall t : (cart _143061 _143063) -> Prop, (@PCROSS _143061 _143062 _143063 (@INTERS (cart _143061 _143062) f) t) = (@COND ((cart _143061 (finite_sum _143062 _143063)) -> Prop) (f = (@EMPTY ((cart _143061 _143062) -> Prop))) (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t) (@INTERS (cart _143061 (finite_sum _143062 _143063)) (@GSPEC ((cart _143061 (finite_sum _143062 _143063)) -> Prop) (fun GEN_PVAR_369 : (cart _143061 (finite_sum _143062 _143063)) -> Prop => exists s : (cart _143061 _143062) -> Prop, @SETSPEC ((cart _143061 (finite_sum _143062 _143063)) -> Prop) GEN_PVAR_369 (@IN ((cart _143061 _143062) -> Prop) s f) (@PCROSS _143061 _143062 _143063 s t))))).
