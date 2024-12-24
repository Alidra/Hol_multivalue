Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4325236 : forall {_103681 _103682 : Type'}, forall s : _103682 -> Prop, forall t : _103681 -> Prop, (@CROSS _103681 _103682 s t) = (@GSPEC (prod _103682 _103681) (fun GEN_PVAR_130 : prod _103682 _103681 => exists x : _103682, exists y : _103681, @SETSPEC (prod _103682 _103681) GEN_PVAR_130 ((@IN _103682 x s) /\ (@IN _103681 y t)) (@pair _103682 _103681 x y))).
