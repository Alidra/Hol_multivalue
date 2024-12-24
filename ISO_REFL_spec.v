Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1075229 : forall {A : Type'}, @ExtensionalityFacts.is_inverse A A (fun x : A => x) (fun x : A => x).
