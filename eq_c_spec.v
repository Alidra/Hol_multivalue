Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5123225 : forall {_114995 _114998 : Type'}, forall t : _114995 -> Prop, forall s : _114998 -> Prop, (@eq_c _114995 _114998 s t) = (exists f : _114998 -> _114995, (forall x : _114998, (@IN _114998 x s) -> @IN _114995 (f x) t) /\ (forall y : _114995, (@IN _114995 y t) -> @ex1 _114998 (fun x : _114998 => (@IN _114998 x s) /\ ((f x) = y)))).
