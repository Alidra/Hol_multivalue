Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4373533 : forall {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : (_104961 -> Prop) -> Prop) (h1 : f = (@EMPTY (_104961 -> Prop))), (forall p1 : _104960, forall p2 : _104961, ((@IN _104960 p1 s) /\ (@IN _104961 p2 (@INTERS _104961 (@EMPTY (_104961 -> Prop))))) = ((@IN _104960 p1 s) /\ (@IN _104961 p2 (@UNIV _104961)))) = ((@CROSS _104961 _104960 s (@INTERS _104961 f)) = (@CROSS _104961 _104960 s (@UNIV _104961))).
