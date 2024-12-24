Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3884187 : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE A s m) /\ ((forall x : A, (@IN A x s) -> @HAS_SIZE B (t x) n) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ (~ (x = y)))) -> @DISJOINT B (t x) (t y)))) -> @HAS_SIZE B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_107 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_107 (@IN A x s) (t x)))) (Nat.mul m n).
