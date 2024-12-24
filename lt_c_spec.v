Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5122043 : forall {_114946 _114947 : Type'}, forall t : _114947 -> Prop, forall s : _114946 -> Prop, (@lt_c _114946 _114947 s t) = ((@le_c _114947 _114946 s t) /\ (~ (@le_c _114946 _114947 t s))).
