Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7017399 : forall {A : Type'}, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> Peano.le (f x) (g x)) /\ (@FINITE A (@GSPEC A (fun GEN_PVAR_299 : A => exists x : A, @SETSPEC A GEN_PVAR_299 ((@IN A x s) /\ (~ ((g x) = (NUMERAL 0)))) x)))) -> Peano.le (@nsum A s f) (@nsum A s g).
