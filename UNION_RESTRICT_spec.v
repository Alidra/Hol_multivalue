Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3239807 : forall {_84925 : Type'}, forall P : _84925 -> Prop, forall s : _84925 -> Prop, forall t : _84925 -> Prop, (@GSPEC _84925 (fun GEN_PVAR_12 : _84925 => exists x : _84925, @SETSPEC _84925 GEN_PVAR_12 ((@IN _84925 x (@UNION _84925 s t)) /\ (P x)) x)) = (@UNION _84925 (@GSPEC _84925 (fun GEN_PVAR_13 : _84925 => exists x : _84925, @SETSPEC _84925 GEN_PVAR_13 ((@IN _84925 x s) /\ (P x)) x)) (@GSPEC _84925 (fun GEN_PVAR_14 : _84925 => exists x : _84925, @SETSPEC _84925 GEN_PVAR_14 ((@IN _84925 x t) /\ (P x)) x))).
