Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4555253 : forall {_107639 _107642 : Type'} (d : _107639), forall s : _107642 -> Prop, forall t : _107639 -> Prop, ((@FINITE _107642 s) /\ (@FINITE _107639 t)) -> (@CARD (_107642 -> _107639) (@GSPEC (_107642 -> _107639) (fun GEN_PVAR_149 : _107642 -> _107639 => exists f : _107642 -> _107639, @SETSPEC (_107642 -> _107639) GEN_PVAR_149 ((forall x : _107642, (@IN _107642 x s) -> @IN _107639 (f x) t) /\ (forall x : _107642, (~ (@IN _107642 x s)) -> (f x) = d)) f))) = (Nat.pow (@CARD _107639 t) (@CARD _107642 s)).
