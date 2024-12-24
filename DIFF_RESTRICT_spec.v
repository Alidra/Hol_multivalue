Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3271962 : forall {_85837 : Type'}, forall P : _85837 -> Prop, forall s : _85837 -> Prop, forall t : _85837 -> Prop, (@GSPEC _85837 (fun GEN_PVAR_18 : _85837 => exists x : _85837, @SETSPEC _85837 GEN_PVAR_18 ((@IN _85837 x (@DIFF _85837 s t)) /\ (P x)) x)) = (@DIFF _85837 (@GSPEC _85837 (fun GEN_PVAR_19 : _85837 => exists x : _85837, @SETSPEC _85837 GEN_PVAR_19 ((@IN _85837 x s) /\ (P x)) x)) (@GSPEC _85837 (fun GEN_PVAR_20 : _85837 => exists x : _85837, @SETSPEC _85837 GEN_PVAR_20 ((@IN _85837 x t) /\ (P x)) x))).
