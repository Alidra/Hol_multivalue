Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4324156 : forall {A B : Type'}, forall s : A -> Prop, forall m : nat, forall t : B -> Prop, forall n : nat, ((@HAS_SIZE A s m) /\ (@HAS_SIZE B t n)) -> @HAS_SIZE (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_129 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_129 ((@IN A x s) /\ (@IN B y t)) (@pair A B x y))) (Nat.mul m n).
