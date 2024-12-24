Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6954254 : forall {_127305 : Type'} (f : _127305 -> nat), forall s : _127305 -> Prop, (@FINITE _127305 s) -> ((@nsum _127305 s f) = (NUMERAL 0)) = (forall x : _127305, (@IN _127305 x s) -> (f x) = (NUMERAL 0)).
