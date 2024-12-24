Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8004229 : forall {_141927 _141928 _141929 : Type'}, forall s : (cart _141927 _141928) -> Prop, forall t : (cart _141927 _141929) -> Prop, forall x : cart _141927 _141928, forall y : cart _141927 _141929, (@IN (cart _141927 (finite_sum _141928 _141929)) (@pastecart _141927 _141928 _141929 x y) (@PCROSS _141927 _141928 _141929 s t)) = ((@IN (cart _141927 _141928) x s) /\ (@IN (cart _141927 _141929) y t)).
