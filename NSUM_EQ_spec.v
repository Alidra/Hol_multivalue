Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6938831 : forall {_127166 : Type'}, forall f : _127166 -> nat, forall g : _127166 -> nat, forall s : _127166 -> Prop, (forall x : _127166, (@IN _127166 x s) -> (f x) = (g x)) -> (@nsum _127166 s f) = (@nsum _127166 s g).
