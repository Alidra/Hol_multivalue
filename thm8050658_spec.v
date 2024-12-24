Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8050658 : forall {_143061 _143062 _143063 : Type'} (t : (cart _143061 _143063) -> Prop) (f : ((cart _143061 _143062) -> Prop) -> Prop) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))), (forall x : cart _143061 _143062, forall y : cart _143061 _143063, ((@IN (cart _143061 _143062) x (@INTERS (cart _143061 _143062) (@EMPTY ((cart _143061 _143062) -> Prop)))) /\ (@IN (cart _143061 _143063) y t)) = ((@IN (cart _143061 _143062) x (@UNIV (cart _143061 _143062))) /\ (@IN (cart _143061 _143063) y t))) = ((@PCROSS _143061 _143062 _143063 (@INTERS (cart _143061 _143062) f) t) = (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t)).
