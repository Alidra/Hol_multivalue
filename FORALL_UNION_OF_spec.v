Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4848609 : forall {_111301 : Type'} (P : ((_111301 -> Prop) -> Prop) -> Prop) (Q : (_111301 -> Prop) -> Prop) (R : (_111301 -> Prop) -> Prop), (forall s : _111301 -> Prop, (@UNION_OF _111301 P Q s) -> R s) = (forall t : (_111301 -> Prop) -> Prop, ((P t) /\ (forall c : _111301 -> Prop, (@IN (_111301 -> Prop) c t) -> Q c)) -> R (@UNIONS _111301 t)).
