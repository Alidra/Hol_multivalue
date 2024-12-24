Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4374535 : forall {_104907 _104908 : Type'} (g : (_104908 -> Prop) -> Prop) (f : (_104907 -> Prop) -> Prop) (h1 : f = (@EMPTY (_104907 -> Prop))), forall p1 : _104907, forall p2 : _104908, ((@IN _104907 p1 (@INTERS _104907 (@EMPTY (_104907 -> Prop)))) /\ (@IN _104908 p2 (@INTERS _104908 g))) = (forall t : _104908 -> Prop, (@IN (_104908 -> Prop) t g) -> (@IN _104907 p1 (@UNIV _104907)) /\ (@IN _104908 p2 t)).
