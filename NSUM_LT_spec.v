Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6934233 : forall {A : Type'}, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((@FINITE A s) /\ ((forall x : A, (@IN A x s) -> Peano.le (f x) (g x)) /\ (exists x : A, (@IN A x s) /\ (Peano.lt (f x) (g x))))) -> Peano.lt (@nsum A s f) (@nsum A s g).
