Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4373351 : forall {_104907 _104908 : Type'} (f : (_104907 -> Prop) -> Prop) (g : (_104908 -> Prop) -> Prop), (forall p1 : _104907, forall p2 : _104908, ((@IN _104907 p1 (@INTERS _104907 f)) /\ (@IN _104908 p2 (@INTERS _104908 g))) = (forall s : _104907 -> Prop, forall t : _104908 -> Prop, ((@IN (_104907 -> Prop) s f) /\ (@IN (_104908 -> Prop) t g)) -> (@IN _104907 p1 s) /\ (@IN _104908 p2 t))) = ((@CROSS _104908 _104907 (@INTERS _104907 f) (@INTERS _104908 g)) = (@INTERS (prod _104907 _104908) (@GSPEC ((prod _104907 _104908) -> Prop) (fun GEN_PVAR_136 : (prod _104907 _104908) -> Prop => exists s : _104907 -> Prop, exists t : _104908 -> Prop, @SETSPEC ((prod _104907 _104908) -> Prop) GEN_PVAR_136 ((@IN (_104907 -> Prop) s f) /\ (@IN (_104908 -> Prop) t g)) (@CROSS _104908 _104907 s t))))).
