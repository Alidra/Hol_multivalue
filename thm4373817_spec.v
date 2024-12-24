Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4373817 : forall {_104960 _104961 : Type'} (f : (_104961 -> Prop) -> Prop) (s : _104960 -> Prop), (forall p1 : _104960, forall p2 : _104961, ((@IN _104960 p1 s) /\ (@IN _104961 p2 (@INTERS _104961 f))) = (forall t : _104961 -> Prop, (@IN (_104961 -> Prop) t f) -> (@IN _104960 p1 s) /\ (@IN _104961 p2 t))) = ((@CROSS _104961 _104960 s (@INTERS _104961 f)) = (@INTERS (prod _104960 _104961) (@GSPEC ((prod _104960 _104961) -> Prop) (fun GEN_PVAR_137 : (prod _104960 _104961) -> Prop => exists t : _104961 -> Prop, @SETSPEC ((prod _104960 _104961) -> Prop) GEN_PVAR_137 (@IN (_104961 -> Prop) t f) (@CROSS _104961 _104960 s t))))).
