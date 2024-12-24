Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6960522 : forall {_127419 : Type'}, forall f : _127419 -> nat, forall s : _127419 -> Prop, forall a : _127419, ((@FINITE _127419 s) /\ (@IN _127419 a s)) -> (Nat.add (f a) (@nsum _127419 (@DELETE _127419 s a) f)) = (@nsum _127419 s f).
