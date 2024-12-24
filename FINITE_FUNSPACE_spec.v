Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4582115 : forall {_107705 _107708 : Type'} (d : _107705), forall s : _107708 -> Prop, forall t : _107705 -> Prop, ((@FINITE _107708 s) /\ (@FINITE _107705 t)) -> @FINITE (_107708 -> _107705) (@GSPEC (_107708 -> _107705) (fun GEN_PVAR_150 : _107708 -> _107705 => exists f : _107708 -> _107705, @SETSPEC (_107708 -> _107705) GEN_PVAR_150 ((forall x : _107708, (@IN _107708 x s) -> @IN _107705 (f x) t) /\ (forall x : _107708, (~ (@IN _107708 x s)) -> (f x) = d)) f)).
