Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3854223 : forall {_99873 : Type'}, forall s : _99873 -> Prop, forall t : _99873 -> Prop, ((@FINITE _99873 s) /\ (@SUBSET _99873 t s)) -> (@CARD _99873 (@DIFF _99873 s t)) = (Nat.sub (@CARD _99873 s) (@CARD _99873 t)).
