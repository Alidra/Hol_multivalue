Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1207999 : forall {_28445 : Type'}, forall h : _28445, forall t : list _28445, (@List.app _28445 (@cons _28445 h (@nil _28445)) t) = (@cons _28445 h t).
