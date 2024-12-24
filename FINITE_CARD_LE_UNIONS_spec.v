Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4606457 : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall m : nat, forall n : nat, ((forall x : A, (@IN A x s) -> (@FINITE B (t x)) /\ (Peano.le (@CARD B (t x)) n)) /\ ((@FINITE A s) /\ (Peano.le (@CARD A s) m))) -> (@FINITE B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_159 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_159 (@IN A x s) (t x))))) /\ (Peano.le (@CARD B (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_160 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_160 (@IN A x s) (t x))))) (Nat.mul m n)).
