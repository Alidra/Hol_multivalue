Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6938734 : forall {_127128 : Type'}, forall f : _127128 -> nat, forall g : _127128 -> nat, forall s : _127128 -> Prop, ((@FINITE _127128 s) /\ ((~ (s = (@EMPTY _127128))) /\ (forall x : _127128, (@IN _127128 x s) -> Peano.lt (f x) (g x)))) -> Peano.lt (@nsum _127128 s f) (@nsum _127128 s g).
