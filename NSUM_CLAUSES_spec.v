Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6924916 : forall {_126486 _126525 : Type'}, (forall f : _126486 -> nat, (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)) /\ (forall x : _126525, forall f : _126525 -> nat, forall s : _126525 -> Prop, (@FINITE _126525 s) -> (@nsum _126525 (@INSERT _126525 x s) f) = (@COND nat (@IN _126525 x s) (@nsum _126525 s f) (Nat.add (f x) (@nsum _126525 s f)))).
