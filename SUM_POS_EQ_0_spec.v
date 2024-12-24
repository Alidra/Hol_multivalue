Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7114167 : forall {_132718 : Type'}, forall f : _132718 -> real, forall s : _132718 -> Prop, ((@FINITE _132718 s) /\ ((forall x : _132718, (@IN _132718 x s) -> real_le (real_of_num (NUMERAL 0)) (f x)) /\ ((@sum _132718 s f) = (real_of_num (NUMERAL 0))))) -> forall x : _132718, (@IN _132718 x s) -> (f x) = (real_of_num (NUMERAL 0)).
