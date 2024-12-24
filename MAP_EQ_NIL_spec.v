Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1190062 : forall {_27823 _27827 : Type'}, forall f : _27827 -> _27823, forall l : list _27827, ((@List.map _27827 _27823 f l) = (@nil _27823)) = (l = (@nil _27827)).
