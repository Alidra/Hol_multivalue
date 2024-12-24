Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4067919 : forall {_102240 _102247 : Type'}, forall P : (_102247 -> Prop) -> Prop, forall f : _102240 -> _102247, forall s : _102240 -> Prop, forall n : nat, (forall t : _102247 -> Prop, ((@FINITE _102247 t) /\ ((Peano.lt (@CARD _102247 t) n) /\ (@SUBSET _102247 t (@IMAGE _102240 _102247 f s)))) -> P t) = (forall t : _102240 -> Prop, ((@FINITE _102240 t) /\ ((Peano.lt (@CARD _102240 t) n) /\ ((@SUBSET _102240 t s) /\ (forall x : _102240, forall y : _102240, ((@IN _102240 x t) /\ (@IN _102240 y t)) -> ((f x) = (f y)) = (x = y))))) -> P (@IMAGE _102240 _102247 f t)).
