Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3395052 : forall {_88162 _88175 : Type'}, forall f : _88175 -> _88162, forall P : _88175 -> Prop, (@GSPEC _88162 (fun GEN_PVAR_24 : _88162 => exists x : _88175, @SETSPEC _88162 GEN_PVAR_24 (P x) (f x))) = (@IMAGE _88175 _88162 f (@GSPEC _88175 (fun GEN_PVAR_25 : _88175 => exists x : _88175, @SETSPEC _88175 GEN_PVAR_25 (P x) x))).
