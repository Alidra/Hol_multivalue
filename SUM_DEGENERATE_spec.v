Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7067459 : forall {_131446 : Type'}, forall f : _131446 -> real, forall s : _131446 -> Prop, (~ (@FINITE _131446 (@GSPEC _131446 (fun GEN_PVAR_311 : _131446 => exists x : _131446, @SETSPEC _131446 GEN_PVAR_311 ((@IN _131446 x s) /\ (~ ((f x) = (real_of_num (NUMERAL 0))))) x)))) -> (@sum _131446 s f) = (real_of_num (NUMERAL 0)).
