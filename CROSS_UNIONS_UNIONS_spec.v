Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4372154 : forall {_104717 _104718 : Type'}, forall f : (_104717 -> Prop) -> Prop, forall g : (_104718 -> Prop) -> Prop, (@CROSS _104718 _104717 (@UNIONS _104717 f) (@UNIONS _104718 g)) = (@UNIONS (prod _104717 _104718) (@GSPEC ((prod _104717 _104718) -> Prop) (fun GEN_PVAR_131 : (prod _104717 _104718) -> Prop => exists s : _104717 -> Prop, exists t : _104718 -> Prop, @SETSPEC ((prod _104717 _104718) -> Prop) GEN_PVAR_131 ((@IN (_104717 -> Prop) s f) /\ (@IN (_104718 -> Prop) t g)) (@CROSS _104718 _104717 s t)))).
