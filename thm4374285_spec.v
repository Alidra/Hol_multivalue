Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4374285 : forall {_105011 _105012 : Type'} (f : (_105011 -> Prop) -> Prop) (t : _105012 -> Prop), (forall p1 : _105011, forall p2 : _105012, ((@IN _105011 p1 (@INTERS _105011 f)) /\ (@IN _105012 p2 t)) = (forall s : _105011 -> Prop, (@IN (_105011 -> Prop) s f) -> (@IN _105011 p1 s) /\ (@IN _105012 p2 t))) = ((@CROSS _105012 _105011 (@INTERS _105011 f) t) = (@INTERS (prod _105011 _105012) (@GSPEC ((prod _105011 _105012) -> Prop) (fun GEN_PVAR_138 : (prod _105011 _105012) -> Prop => exists s : _105011 -> Prop, @SETSPEC ((prod _105011 _105012) -> Prop) GEN_PVAR_138 (@IN (_105011 -> Prop) s f) (@CROSS _105012 _105011 s t))))).
