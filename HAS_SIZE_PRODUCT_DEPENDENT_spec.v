Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4318348 : forall {A B : Type'}, forall s : A -> Prop, forall m : nat, forall t : A -> B -> Prop, forall n : nat, ((@HAS_SIZE A s m) /\ (forall x : A, (@IN A x s) -> @HAS_SIZE B (t x) n)) -> @HAS_SIZE (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_121 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_121 ((@IN A x s) /\ (@IN B y (t x))) (@pair A B x y))) (Nat.mul m n).
