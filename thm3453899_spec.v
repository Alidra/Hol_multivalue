Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3453899 : forall {A : Type'} (s : (A -> Prop) -> Prop) (x : A), (fun x' : A => (@IN A x' (@UNIONS A s)) = (exists t : A -> Prop, (@IN (A -> Prop) t s) /\ (@IN A x' t))) x.
