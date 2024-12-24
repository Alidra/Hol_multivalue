Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7614851 : forall {A B : Type'}, (forall a : cart A B, (@mk_cart A B (@dest_cart A B a)) = a) /\ (forall r : (finite_image B) -> A, True = ((@dest_cart A B (@mk_cart A B r)) = r)).
