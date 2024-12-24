Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211668 : forall {A : Type'} (s : (A -> Prop) -> Prop) (x : A), (fun x' : A => (@IN A x' (@INTERS A s)) = (forall t : A -> Prop, (@IN (A -> Prop) t s) -> @IN A x' t)) x.
