Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1104044 : forall {_25409 _25416 : Type'} (P : _25409 -> _25416 -> Prop) (l2 : list _25416), ((fun l2' : list _25416 => (@ALL2 _25409 _25416 P (@nil _25409) l2') = (l2' = (@nil _25416))) l2) = ((@ALL2 _25409 _25416 P (@nil _25409) l2) = (l2 = (@nil _25416))).
