Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4521678 : forall {A B : Type'}, forall d : B, forall n : nat, forall t : B -> Prop, forall m : nat, forall s : A -> Prop, ((@HAS_SIZE A s m) /\ (@HAS_SIZE B t n)) -> @HAS_SIZE (A -> B) (@GSPEC (A -> B) (fun GEN_PVAR_148 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_148 ((forall x : A, (@IN A x s) -> @IN B (f x) t) /\ (forall x : A, (~ (@IN A x s)) -> (f x) = d)) f)) (Nat.pow n m).
