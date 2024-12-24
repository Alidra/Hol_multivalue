Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1100097 : forall {_25287 : Type'} (h : _25287) (t : list _25287), ((@NULL _25287 (@nil _25287)) = True) /\ ((@NULL _25287 (@cons _25287 h t)) = False).
