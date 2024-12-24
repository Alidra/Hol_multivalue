Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5712802 : forall {A : Type'}, forall op : A -> A -> A, (@monoidal A op) = ((forall x : A, forall y : A, (op x y) = (op y x)) /\ ((forall x : A, forall y : A, forall z : A, (op x (op y z)) = (op (op x y) z)) /\ (forall x : A, (op (@neutral A op) x) = x))).
