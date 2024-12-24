Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4456752 : forall {A B K : Type'}, forall k : K -> Prop, forall f : K -> A -> B, (@product_map A B K k f) = (fun x : K -> A => @RESTRICTION K B k (fun i : K => f i (x i))).
