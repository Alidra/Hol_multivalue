Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3393993 : forall {_88128 _88132 : Type'}, forall f : _88128 -> _88132, forall s : _88128 -> Prop, (@GSPEC _88132 (fun GEN_PVAR_23 : _88132 => exists x : _88128, @SETSPEC _88132 GEN_PVAR_23 (@IN _88128 x s) (f x))) = (@IMAGE _88128 _88132 f s).
