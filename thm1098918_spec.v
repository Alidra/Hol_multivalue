Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1098918 : forall {_25251 : Type'}, forall h : _25251, forall t : list _25251, (@List.removelast _25251 (@cons _25251 h t)) = (@COND (list _25251) (t = (@nil _25251)) (@nil _25251) (@cons _25251 h (@List.removelast _25251 t))).
