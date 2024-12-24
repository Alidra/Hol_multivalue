Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3238518 : forall {_84841 : Type'}, forall s : _84841 -> Prop, forall t : _84841 -> Prop, forall u : _84841 -> Prop, (@SUBSET _84841 (@UNION _84841 s t) u) = ((@SUBSET _84841 s u) /\ (@SUBSET _84841 t u)).
