Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7178808 : forall {_135252 : Type'}, forall f : _135252 -> real, forall s : _135252 -> Prop, forall t : _135252 -> Prop, ((@FINITE _135252 s) /\ ((@FINITE _135252 t) /\ (forall x : _135252, (@IN _135252 x (@INTER _135252 s t)) -> (f x) = (real_of_num (NUMERAL 0))))) -> (@sum _135252 (@UNION _135252 s t) f) = (real_add (@sum _135252 s f) (@sum _135252 t f)).
