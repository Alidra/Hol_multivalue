Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4015146 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall y : B, (@IN B y t) -> @ex1 A (fun x : A => (@IN A x s) /\ ((f x) = y))))) -> (@CARD B t) = (@CARD A s).
