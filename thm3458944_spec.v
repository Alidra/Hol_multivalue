Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3458944 : forall {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : _89534 -> _89520 -> Prop), (@UNIONS _89520 (@GSPEC (_89520 -> Prop) (fun GEN_PVAR_49 : _89520 -> Prop => exists x : _89534, @SETSPEC (_89520 -> Prop) GEN_PVAR_49 (P x) (f x)))) = (@GSPEC _89520 (fun GEN_PVAR_50 : _89520 => exists a : _89520, @SETSPEC _89520 GEN_PVAR_50 (exists x : _89534, (P x) /\ (@IN _89520 a (f x))) a)).
