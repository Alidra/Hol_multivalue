Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6924730 : forall {_126453 : Type'}, forall f : _126453 -> nat, forall s : _126453 -> Prop, (~ (@FINITE _126453 (@GSPEC _126453 (fun GEN_PVAR_284 : _126453 => exists x : _126453, @SETSPEC _126453 GEN_PVAR_284 ((@IN _126453 x s) /\ (~ ((f x) = (NUMERAL 0)))) x)))) -> (@nsum _126453 s f) = (NUMERAL 0).
