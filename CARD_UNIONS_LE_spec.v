Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3934511 : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE A s m) /\ (forall x : A, (@IN A x s) -> (@FINITE B (t x)) /\ (Peano.le (@CARD B (t x)) n))) -> Peano.le (@CARD B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_113 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_113 (@IN A x s) (t x))))) (Nat.mul m n).
