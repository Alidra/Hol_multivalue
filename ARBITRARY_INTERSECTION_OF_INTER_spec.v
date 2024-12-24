Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4869076 : forall {_111835 : Type'}, forall P : (_111835 -> Prop) -> Prop, forall s : _111835 -> Prop, forall t : _111835 -> Prop, ((@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) /\ (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P t)) -> @INTERSECTION_OF _111835 (@ARBITRARY _111835) P (@INTER _111835 s t).
