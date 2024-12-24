Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem297 : forall {_216 : Type'} (P : _216 -> Prop) (Q : Prop), (forall x : _216, (P x) -> Q) = ((exists x : _216, P x) -> Q).
