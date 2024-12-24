Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21052 : forall (p : Prop) (h1 : p = True), ((True -> ~ True) = (~ True)) = ((p -> ~ p) = (~ p)).
