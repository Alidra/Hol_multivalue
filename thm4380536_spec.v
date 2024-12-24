Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4380536 : forall {_105011 _105012 : Type'}, forall f : (_105011 -> Prop) -> Prop, forall t : _105012 -> Prop, (@CROSS _105012 _105011 (@INTERS _105011 f) t) = (@COND ((prod _105011 _105012) -> Prop) (f = (@EMPTY (_105011 -> Prop))) (@CROSS _105012 _105011 (@UNIV _105011) t) (@INTERS (prod _105011 _105012) (@GSPEC ((prod _105011 _105012) -> Prop) (fun GEN_PVAR_138 : (prod _105011 _105012) -> Prop => exists s : _105011 -> Prop, @SETSPEC ((prod _105011 _105012) -> Prop) GEN_PVAR_138 (@IN (_105011 -> Prop) s f) (@CROSS _105012 _105011 s t))))).
