Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3261090 : forall {_85450 : Type'}, forall P : _85450 -> Prop, forall s : _85450 -> Prop, forall t : _85450 -> Prop, (@GSPEC _85450 (fun GEN_PVAR_15 : _85450 => exists x : _85450, @SETSPEC _85450 GEN_PVAR_15 ((@IN _85450 x (@INTER _85450 s t)) /\ (P x)) x)) = (@INTER _85450 (@GSPEC _85450 (fun GEN_PVAR_16 : _85450 => exists x : _85450, @SETSPEC _85450 GEN_PVAR_16 ((@IN _85450 x s) /\ (P x)) x)) (@GSPEC _85450 (fun GEN_PVAR_17 : _85450 => exists x : _85450, @SETSPEC _85450 GEN_PVAR_17 ((@IN _85450 x t) /\ (P x)) x))).
