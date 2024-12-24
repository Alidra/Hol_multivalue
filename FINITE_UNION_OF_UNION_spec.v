Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4887282 : forall {_112456 : Type'}, forall P : (_112456 -> Prop) -> Prop, forall s : _112456 -> Prop, forall t : _112456 -> Prop, ((@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) /\ (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t)) -> @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P (@UNION _112456 s t).
