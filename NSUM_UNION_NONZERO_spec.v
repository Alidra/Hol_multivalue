Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7018613 : forall {_129614 : Type'}, forall f : _129614 -> nat, forall s : _129614 -> Prop, forall t : _129614 -> Prop, ((@FINITE _129614 s) /\ ((@FINITE _129614 t) /\ (forall x : _129614, (@IN _129614 x (@INTER _129614 s t)) -> (f x) = (NUMERAL 0)))) -> (@nsum _129614 (@UNION _129614 s t) f) = (Nat.add (@nsum _129614 s f) (@nsum _129614 t f)).
