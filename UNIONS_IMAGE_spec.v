Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3452302 : forall {_89422 _89438 : Type'}, forall f : _89438 -> _89422 -> Prop, forall s : _89438 -> Prop, (@UNIONS _89422 (@IMAGE _89438 (_89422 -> Prop) f s)) = (@GSPEC _89422 (fun GEN_PVAR_47 : _89422 => exists y : _89422, @SETSPEC _89422 GEN_PVAR_47 (exists x : _89438, (@IN _89438 x s) /\ (@IN _89422 y (f x))) y)).
