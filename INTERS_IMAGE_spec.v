Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3453847 : forall {_89465 _89481 : Type'}, forall f : _89481 -> _89465 -> Prop, forall s : _89481 -> Prop, (@INTERS _89465 (@IMAGE _89481 (_89465 -> Prop) f s)) = (@GSPEC _89465 (fun GEN_PVAR_48 : _89465 => exists y : _89465, @SETSPEC _89465 GEN_PVAR_48 (forall x : _89481, (@IN _89481 x s) -> @IN _89465 y (f x)) y)).
