Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3405756 : forall {_88435 _88436 : Type'}, forall P : _88436 -> _88435 -> Prop, forall a : _88436, forall b : _88435, (@IN (prod _88436 _88435) (@pair _88436 _88435 a b) (@GSPEC (prod _88436 _88435) (fun GEN_PVAR_31 : prod _88436 _88435 => exists x : _88436, exists y : _88435, @SETSPEC (prod _88436 _88435) GEN_PVAR_31 (P x y) (@pair _88436 _88435 x y)))) = (P a b).
