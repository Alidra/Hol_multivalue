Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4323219 : forall {A B C : Type'}, forall f : A -> B -> C, forall s : A -> Prop, forall t : A -> B -> Prop, ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> @FINITE B (t x))) -> @FINITE C (@GSPEC C (fun GEN_PVAR_126 : C => exists x : A, exists y : B, @SETSPEC C GEN_PVAR_126 ((@IN A x s) /\ (@IN B y (t x))) (f x y))).
