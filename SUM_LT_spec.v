Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7073063 : forall {A : Type'}, forall f : A -> real, forall g : A -> real, forall s : A -> Prop, ((@FINITE A s) /\ ((forall x : A, (@IN A x s) -> real_le (f x) (g x)) /\ (exists x : A, (@IN A x s) /\ (real_lt (f x) (g x))))) -> real_lt (@sum A s f) (@sum A s g).
