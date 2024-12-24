Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1108949 : forall {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727), ((@ZIP _25719 _25727 (@nil _25719) l2) = (@nil (prod _25719 _25727))) /\ ((@ZIP _25719 _25727 (@cons _25719 h1' t1) l2) = (@cons (prod _25719 _25727) (@pair _25719 _25727 h1' (@hd _25727 l2)) (@ZIP _25719 _25727 t1 (@tl _25727 l2)))).
