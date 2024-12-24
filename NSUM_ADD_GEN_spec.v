Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6930693 : forall {_126816 : Type'}, forall f : _126816 -> nat, forall g : _126816 -> nat, forall s : _126816 -> Prop, ((@FINITE _126816 (@GSPEC _126816 (fun GEN_PVAR_285 : _126816 => exists x : _126816, @SETSPEC _126816 GEN_PVAR_285 ((@IN _126816 x s) /\ (~ ((f x) = (NUMERAL 0)))) x))) /\ (@FINITE _126816 (@GSPEC _126816 (fun GEN_PVAR_286 : _126816 => exists x : _126816, @SETSPEC _126816 GEN_PVAR_286 ((@IN _126816 x s) /\ (~ ((g x) = (NUMERAL 0)))) x)))) -> (@nsum _126816 s (fun x : _126816 => Nat.add (f x) (g x))) = (Nat.add (@nsum _126816 s f) (@nsum _126816 s g)).
