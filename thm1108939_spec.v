Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1108939 : forall {_25719 _25727 : Type'} (l2 : list _25727), (@ZIP _25719 _25727 (@nil _25719) l2) = (@nil (prod _25719 _25727)).