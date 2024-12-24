Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4668 : forall {_910 : Type'}, forall P : _910 -> Prop, forall a : _910, (forall x : _910, (a = x) -> P x) = (P a).
