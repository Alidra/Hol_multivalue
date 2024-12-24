Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7927999 : forall {A Z : Type'}, forall f : (finite_sum A A) -> Z, exists fn : (tybit0 A) -> Z, forall a : finite_sum A A, (fn (@mktybit0 A a)) = (f a).
