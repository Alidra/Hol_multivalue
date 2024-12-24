Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20930 : forall (b : Prop) (a : Prop) (h1 : a = True), (((~ True) \/ (~ b)) = (~ (True /\ b))) = (((~ a) \/ (~ b)) = (~ (a /\ b))).
