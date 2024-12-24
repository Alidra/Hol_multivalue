Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6933015 : forall {_127006 : Type'}, forall f : _127006 -> nat, forall g : _127006 -> nat, forall s : _127006 -> Prop, ((@FINITE _127006 s) /\ (forall x : _127006, (@IN _127006 x s) -> Peano.le (f x) (g x))) -> Peano.le (@nsum _127006 s f) (@nsum _127006 s g).
