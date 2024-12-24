Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6929990 : forall {_126606 : Type'}, forall f : _126606 -> nat, forall s : _126606 -> Prop, forall t : _126606 -> Prop, ((@FINITE _126606 s) /\ (@SUBSET _126606 t s)) -> (@nsum _126606 (@DIFF _126606 s t) f) = (Nat.sub (@nsum _126606 s f) (@nsum _126606 t f)).
