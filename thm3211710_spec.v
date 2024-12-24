Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211710 : forall {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A), (fun x' : A => (@IN A x' (@INTER A s t)) = ((@IN A x' s) /\ (@IN A x' t))) x.
