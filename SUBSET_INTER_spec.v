Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3260071 : forall {_85366 : Type'}, forall s : _85366 -> Prop, forall t : _85366 -> Prop, forall u : _85366 -> Prop, (@SUBSET _85366 s (@INTER _85366 t u)) = ((@SUBSET _85366 s t) /\ (@SUBSET _85366 s u)).
