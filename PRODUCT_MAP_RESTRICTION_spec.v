Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4457258 : forall {A B K : Type'}, forall f : K -> A -> B, forall k : K -> Prop, forall x : K -> A, (@product_map A B K k f (@RESTRICTION K A k x)) = (@RESTRICTION K B k (fun i : K => f i (x i))).
