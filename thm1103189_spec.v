Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1103189 : forall {_25376 : Type'}, forall h : _25376, forall x : _25376, forall t : list _25376, (@List.In _25376 x (@cons _25376 h t)) = ((x = h) \/ (@List.In _25376 x t)).
