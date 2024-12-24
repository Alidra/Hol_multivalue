Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1207006 : forall {_28337 : Type'}, forall l : list _28337, (~ (l = (@nil _28337))) -> l = (@cons _28337 (@hd _28337 l) (@tl _28337 l)).
