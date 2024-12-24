Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3183080 : forall {A : Type'} (P : A -> Prop) (x : A), (fun x' : A => (@IN A x' P) = (P x')) x.
