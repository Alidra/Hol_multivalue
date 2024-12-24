Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8039091 : forall {_142619 _142620 _142621 _142655 _142656 _142657 : Type'}, (forall s : (cart _142619 _142620) -> Prop, forall t : (cart _142619 _142621) -> Prop, forall u : (cart _142619 _142621) -> Prop, (@PCROSS _142619 _142620 _142621 s (@DIFF (cart _142619 _142621) t u)) = (@DIFF (cart _142619 (finite_sum _142620 _142621)) (@PCROSS _142619 _142620 _142621 s t) (@PCROSS _142619 _142620 _142621 s u))) /\ (forall s : (cart _142655 _142656) -> Prop, forall t : (cart _142655 _142656) -> Prop, forall u : (cart _142655 _142657) -> Prop, (@PCROSS _142655 _142656 _142657 (@DIFF (cart _142655 _142656) s t) u) = (@DIFF (cart _142655 (finite_sum _142656 _142657)) (@PCROSS _142655 _142656 _142657 s u) (@PCROSS _142655 _142656 _142657 t u))).
