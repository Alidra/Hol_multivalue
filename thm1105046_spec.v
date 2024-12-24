Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1105046 : forall {_25498 _25501 _25508 : Type'}, (forall f : _25501 -> _25508 -> _25498, forall l : list _25508, (@MAP2 _25498 _25501 _25508 f (@nil _25501) l) = (@nil _25498)) /\ (forall h1' : _25501, forall f : _25501 -> _25508 -> _25498, forall t1 : list _25501, forall l : list _25508, (@MAP2 _25498 _25501 _25508 f (@cons _25501 h1' t1) l) = (@cons _25498 (f h1' (@hd _25508 l)) (@MAP2 _25498 _25501 _25508 f t1 (@tl _25508 l)))).
