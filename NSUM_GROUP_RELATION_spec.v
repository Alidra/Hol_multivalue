Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7002618 : forall {A B : Type'}, forall R : A -> B -> Prop, forall g : A -> nat, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> @ex1 B (fun y : B => (@IN B y t) /\ (R x y)))) -> (@nsum B t (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_297 : A => exists x : A, @SETSPEC A GEN_PVAR_297 ((@IN A x s) /\ (R x y)) x)) g)) = (@nsum A s g).
