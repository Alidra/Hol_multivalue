Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4790288 : forall {_110409 : Type'}, forall l1 : list _110409, forall l2 : list _110409, (@set_of_list _110409 (@List.app _110409 l1 l2)) = (@UNION _110409 (@set_of_list _110409 l1) (@set_of_list _110409 l2)).
