Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4851595 : forall {_111337 : Type'} (P : ((_111337 -> Prop) -> Prop) -> Prop) (Q : (_111337 -> Prop) -> Prop) (R : (_111337 -> Prop) -> Prop), (forall s : _111337 -> Prop, (@INTERSECTION_OF _111337 P Q s) -> R s) = (forall t : (_111337 -> Prop) -> Prop, ((P t) /\ (forall c : _111337 -> Prop, (@IN (_111337 -> Prop) c t) -> Q c)) -> R (@INTERS _111337 t)).
