Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7157061 : forall {_133899 : Type'}, forall P : _133899 -> Prop, forall s : _133899 -> Prop, forall f : _133899 -> real, (@sum _133899 (@GSPEC _133899 (fun GEN_PVAR_316 : _133899 => exists x : _133899, @SETSPEC _133899 GEN_PVAR_316 ((@IN _133899 x s) /\ (P x)) x)) f) = (@sum _133899 s (fun x : _133899 => @COND real (P x) (f x) (real_of_num (NUMERAL 0)))).
