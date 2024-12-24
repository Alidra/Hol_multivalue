Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3400385 : forall {_88341 _88367 : Type'}, (forall a : _88341, (@GSPEC _88341 (fun GEN_PVAR_28 : _88341 => exists x : _88341, @SETSPEC _88341 GEN_PVAR_28 (x = a) x)) = (@INSERT _88341 a (@EMPTY _88341))) /\ (forall a : _88367, (@GSPEC _88367 (fun GEN_PVAR_29 : _88367 => exists x : _88367, @SETSPEC _88367 GEN_PVAR_29 (a = x) x)) = (@INSERT _88367 a (@EMPTY _88367))).
