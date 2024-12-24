Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4868729 : forall {_111767 : Type'}, forall P : (_111767 -> Prop) -> Prop, forall s : _111767 -> Prop, forall t : _111767 -> Prop, ((@UNION_OF _111767 (@ARBITRARY _111767) P s) /\ (@UNION_OF _111767 (@ARBITRARY _111767) P t)) -> @UNION_OF _111767 (@ARBITRARY _111767) P (@UNION _111767 s t).
