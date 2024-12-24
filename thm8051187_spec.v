Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8051187 : forall {_142951 _142952 _142953 : Type'} (g : ((cart _142951 _142953) -> Prop) -> Prop) (f : ((cart _142951 _142952) -> Prop) -> Prop) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))), forall x : cart _142951 _142952, forall y : cart _142951 _142953, ((@IN (cart _142951 _142952) x (@INTERS (cart _142951 _142952) (@EMPTY ((cart _142951 _142952) -> Prop)))) /\ (@IN (cart _142951 _142953) y (@INTERS (cart _142951 _142953) g))) = (forall t : (cart _142951 _142953) -> Prop, (@IN ((cart _142951 _142953) -> Prop) t g) -> (@IN (cart _142951 _142952) x (@UNIV (cart _142951 _142952))) /\ (@IN (cart _142951 _142953) y t)).
