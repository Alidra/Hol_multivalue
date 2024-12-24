Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1108935 : forall {_25719 _25727 : Type'}, forall h1' : _25719, forall t1 : list _25719, forall l2 : list _25727, (@ZIP _25719 _25727 (@cons _25719 h1' t1) l2) = (@cons (prod _25719 _25727) (@pair _25719 _25727 h1' (@hd _25727 l2)) (@ZIP _25719 _25727 t1 (@tl _25727 l2))).
