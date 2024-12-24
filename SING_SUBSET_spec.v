Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3221020 : forall {_84443 : Type'}, forall s : _84443 -> Prop, forall x : _84443, (@SUBSET _84443 (@INSERT _84443 x (@EMPTY _84443)) s) = (@IN _84443 x s).
