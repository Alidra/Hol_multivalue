Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3399787 : forall {_88312 : Type'}, (forall x : _88312, (@IN _88312 x (@GSPEC _88312 (fun GEN_PVAR_27 : _88312 => exists x' : _88312, @SETSPEC _88312 GEN_PVAR_27 True x'))) = (@IN _88312 x (@UNIV _88312))) = ((@GSPEC _88312 (fun GEN_PVAR_27 : _88312 => exists x : _88312, @SETSPEC _88312 GEN_PVAR_27 True x)) = (@UNIV _88312)).
