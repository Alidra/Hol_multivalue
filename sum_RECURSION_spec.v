Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1068060 : forall {A B Z : Type'}, forall INL' : A -> Z, forall INR' : B -> Z, exists fn : (Datatypes.sum A B) -> Z, (forall a : A, (fn (@inl A B a)) = (INL' a)) /\ (forall a : B, (fn (@inr A B a)) = (INR' a)).
