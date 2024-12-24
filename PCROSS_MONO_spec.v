Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8010834 : forall {_142122 _142123 _142124 : Type'}, forall s : (cart _142122 _142123) -> Prop, forall t : (cart _142122 _142124) -> Prop, forall s' : (cart _142122 _142123) -> Prop, forall t' : (cart _142122 _142124) -> Prop, ((@SUBSET (cart _142122 _142123) s s') /\ (@SUBSET (cart _142122 _142124) t t')) -> @SUBSET (cart _142122 (finite_sum _142123 _142124)) (@PCROSS _142122 _142123 _142124 s t) (@PCROSS _142122 _142123 _142124 s' t').
