Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7058518 : forall {A : Type'}, forall n : nat, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> @eq2 nat (f x) (g x) (num_mod n))) -> @eq2 nat (@nsum A s f) (@nsum A s g) (num_mod n).
