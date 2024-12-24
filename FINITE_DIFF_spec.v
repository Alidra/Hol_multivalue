Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3734933 : forall {_97970 : Type'}, forall s : _97970 -> Prop, forall t : _97970 -> Prop, (@FINITE _97970 s) -> @FINITE _97970 (@DIFF _97970 s t).
