Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3221162 : forall {_84465 : Type'}, forall s : _84465 -> Prop, forall P : _84465 -> Prop, @SUBSET _84465 (@GSPEC _84465 (fun GEN_PVAR_11 : _84465 => exists x : _84465, @SETSPEC _84465 GEN_PVAR_11 ((@IN _84465 x s) /\ (P x)) x)) s.
