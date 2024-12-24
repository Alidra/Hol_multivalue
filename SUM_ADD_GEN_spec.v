Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7069012 : forall {_131804 : Type'}, forall f : _131804 -> real, forall g : _131804 -> real, forall s : _131804 -> Prop, ((@FINITE _131804 (@GSPEC _131804 (fun GEN_PVAR_312 : _131804 => exists x : _131804, @SETSPEC _131804 GEN_PVAR_312 ((@IN _131804 x s) /\ (~ ((f x) = (real_of_num (NUMERAL 0))))) x))) /\ (@FINITE _131804 (@GSPEC _131804 (fun GEN_PVAR_313 : _131804 => exists x : _131804, @SETSPEC _131804 GEN_PVAR_313 ((@IN _131804 x s) /\ (~ ((g x) = (real_of_num (NUMERAL 0))))) x)))) -> (@sum _131804 s (fun x : _131804 => real_add (f x) (g x))) = (real_add (@sum _131804 s f) (@sum _131804 s g)).
