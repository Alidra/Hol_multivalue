Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6991883 : forall {_128402 _128403 : Type'}, forall R : _128403 -> _128402 -> Prop, forall f : _128403 -> _128402 -> nat, forall s : _128403 -> Prop, forall t : _128402 -> Prop, ((@FINITE _128403 s) /\ (@FINITE _128402 t)) -> (@nsum _128403 s (fun x : _128403 => @nsum _128402 (@GSPEC _128402 (fun GEN_PVAR_288 : _128402 => exists y : _128402, @SETSPEC _128402 GEN_PVAR_288 ((@IN _128402 y t) /\ (R x y)) y)) (fun y : _128402 => f x y))) = (@nsum _128402 t (fun y : _128402 => @nsum _128403 (@GSPEC _128403 (fun GEN_PVAR_289 : _128403 => exists x : _128403, @SETSPEC _128403 GEN_PVAR_289 ((@IN _128403 x s) /\ (R x y)) x)) (fun x : _128403 => f x y))).
