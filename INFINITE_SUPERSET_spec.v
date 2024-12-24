Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3735653 : forall {_97990 : Type'}, forall s : _97990 -> Prop, forall t : _97990 -> Prop, ((@INFINITE _97990 s) /\ (@SUBSET _97990 s t)) -> @INFINITE _97990 t.
