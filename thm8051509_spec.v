Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8051509 : forall {_142951 _142952 _142953 : Type'} (f : ((cart _142951 _142952) -> Prop) -> Prop) (g : ((cart _142951 _142953) -> Prop) -> Prop) (h1 : ~ (f = (@EMPTY ((cart _142951 _142952) -> Prop)))) (h2 : g = (@EMPTY ((cart _142951 _142953) -> Prop))), forall x : cart _142951 _142952, forall y : cart _142951 _142953, ((@IN (cart _142951 _142952) x (@INTERS (cart _142951 _142952) f)) /\ (@IN (cart _142951 _142953) y (@INTERS (cart _142951 _142953) (@EMPTY ((cart _142951 _142953) -> Prop))))) = (forall s : (cart _142951 _142952) -> Prop, (@IN ((cart _142951 _142952) -> Prop) s f) -> (@IN (cart _142951 _142952) x s) /\ (@IN (cart _142951 _142953) y (@UNIV (cart _142951 _142953)))).
