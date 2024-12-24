Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8039577 : forall {_142693 _142694 _142695 : Type'}, forall s : (cart _142693 _142694) -> Prop, forall s' : (cart _142693 _142694) -> Prop, forall t : (cart _142693 _142695) -> Prop, forall t' : (cart _142693 _142695) -> Prop, (@INTER (cart _142693 (finite_sum _142694 _142695)) (@PCROSS _142693 _142694 _142695 s t) (@PCROSS _142693 _142694 _142695 s' t')) = (@PCROSS _142693 _142694 _142695 (@INTER (cart _142693 _142694) s s') (@INTER (cart _142693 _142695) t t')).
