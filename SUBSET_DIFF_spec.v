Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3270702 : forall {_85745 : Type'}, forall s : _85745 -> Prop, forall t : _85745 -> Prop, @SUBSET _85745 (@DIFF _85745 s t) s.
