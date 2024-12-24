Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1202159 : forall {_28076 : Type'}, forall l : list _28076, (~ (l = (@nil _28076))) -> (@List.app _28076 (@List.removelast _28076 l) (@cons _28076 (@LAST _28076 l) (@nil _28076))) = l.
