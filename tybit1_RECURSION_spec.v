Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7931326 : forall {A Z : Type'}, forall f : (finite_sum (finite_sum A A) unit) -> Z, exists fn : (tybit1 A) -> Z, forall a : finite_sum (finite_sum A A) unit, (fn (@mktybit1 A a)) = (f a).
