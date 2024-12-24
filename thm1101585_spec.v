Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1101585 : forall {_25328 : Type'}, forall h : _25328, forall P : _25328 -> Prop, forall t : list _25328, (@EX _25328 P (@cons _25328 h t)) = ((P h) \/ (@EX _25328 P t)).
