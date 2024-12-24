Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7158000 : forall {_133990 _133991 : Type'}, forall R : _133991 -> _133990 -> Prop, forall f : _133991 -> _133990 -> real, forall s : _133991 -> Prop, forall t : _133990 -> Prop, ((@FINITE _133991 s) /\ (@FINITE _133990 t)) -> (@sum _133991 s (fun x : _133991 => @sum _133990 (@GSPEC _133990 (fun GEN_PVAR_317 : _133990 => exists y : _133990, @SETSPEC _133990 GEN_PVAR_317 ((@IN _133990 y t) /\ (R x y)) y)) (fun y : _133990 => f x y))) = (@sum _133990 t (fun y : _133990 => @sum _133991 (@GSPEC _133991 (fun GEN_PVAR_318 : _133991 => exists x : _133991, @SETSPEC _133991 GEN_PVAR_318 ((@IN _133991 x s) /\ (R x y)) x)) (fun x : _133991 => f x y))).
