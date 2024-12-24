Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7927982 : forall {A : Type'}, forall P : (tybit0 A) -> Prop, (forall a : finite_sum A A, P (@mktybit0 A a)) -> forall x : tybit0 A, P x.
