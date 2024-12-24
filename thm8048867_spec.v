Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8048867 : forall {_142951 _142952 : Type'} (f : ((cart _142951 _142952) -> Prop) -> Prop) (h1 : ~ (f = (@EMPTY ((cart _142951 _142952) -> Prop)))), ~ (f = (@EMPTY ((cart _142951 _142952) -> Prop))).
