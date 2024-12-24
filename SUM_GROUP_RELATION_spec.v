Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7168710 : forall {A B : Type'}, forall R : A -> B -> Prop, forall g : A -> real, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> @ex1 B (fun y : B => (@IN B y t) /\ (R x y)))) -> (@sum B t (fun y : B => @sum A (@GSPEC A (fun GEN_PVAR_326 : A => exists x : A, @SETSPEC A GEN_PVAR_326 ((@IN A x s) /\ (R x y)) x)) g)) = (@sum A s g).
