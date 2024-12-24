Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3458943 : forall {_89578 _89597 _89598 : Type'} (P : _89598 -> _89597 -> Prop) (f : _89598 -> _89597 -> _89578 -> Prop), (@UNIONS _89578 (@GSPEC (_89578 -> Prop) (fun GEN_PVAR_51 : _89578 -> Prop => exists x : _89598, exists y : _89597, @SETSPEC (_89578 -> Prop) GEN_PVAR_51 (P x y) (f x y)))) = (@GSPEC _89578 (fun GEN_PVAR_52 : _89578 => exists a : _89578, @SETSPEC _89578 GEN_PVAR_52 (exists x : _89598, exists y : _89597, (P x y) /\ (@IN _89578 a (f x y))) a)).
