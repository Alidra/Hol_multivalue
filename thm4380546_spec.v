Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4380546 : forall {_104960 _104961 : Type'}, forall s : _104960 -> Prop, forall f : (_104961 -> Prop) -> Prop, (@CROSS _104961 _104960 s (@INTERS _104961 f)) = (@COND ((prod _104960 _104961) -> Prop) (f = (@EMPTY (_104961 -> Prop))) (@CROSS _104961 _104960 s (@UNIV _104961)) (@INTERS (prod _104960 _104961) (@GSPEC ((prod _104960 _104961) -> Prop) (fun GEN_PVAR_137 : (prod _104960 _104961) -> Prop => exists t : _104961 -> Prop, @SETSPEC ((prod _104960 _104961) -> Prop) GEN_PVAR_137 (@IN (_104961 -> Prop) t f) (@CROSS _104961 _104960 s t))))).
