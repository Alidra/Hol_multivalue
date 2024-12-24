Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3399757 : forall {_88295 : Type'}, forall x : _88295, (@IN _88295 x (@GSPEC _88295 (fun GEN_PVAR_26 : _88295 => exists x' : _88295, @SETSPEC _88295 GEN_PVAR_26 False x'))) = (@IN _88295 x (@EMPTY _88295)).
