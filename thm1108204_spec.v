Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1108204 : forall {_25645 _25647 _25655 : Type'}, (forall f : _25647 -> _25655 -> _25645 -> _25645, forall l2 : list _25655, forall b : _25645, (@ITLIST2 _25645 _25647 _25655 f (@nil _25647) l2 b) = b) /\ (forall h1' : _25647, forall f : _25647 -> _25655 -> _25645 -> _25645, forall t1 : list _25647, forall l2 : list _25655, forall b : _25645, (@ITLIST2 _25645 _25647 _25655 f (@cons _25647 h1' t1) l2 b) = (f h1' (@hd _25655 l2) (@ITLIST2 _25645 _25647 _25655 f t1 (@tl _25655 l2) b))).
