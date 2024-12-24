Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4887666 : forall {_112528 : Type'}, forall P : (_112528 -> Prop) -> Prop, forall s : _112528 -> Prop, forall t : _112528 -> Prop, ((@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P s) /\ (@INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P t)) -> @INTERSECTION_OF _112528 (@FINITE (_112528 -> Prop)) P (@INTER _112528 s t).
