Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3197563 : forall {A : Type'}, ((@FINITE A (@EMPTY A)) /\ (forall x : A, forall s : A -> Prop, (@FINITE A s) -> @FINITE A (@INSERT A x s))) /\ ((forall FINITE' : (A -> Prop) -> Prop, ((FINITE' (@EMPTY A)) /\ (forall x : A, forall s : A -> Prop, (FINITE' s) -> FINITE' (@INSERT A x s))) -> forall a : A -> Prop, (@FINITE A a) -> FINITE' a) /\ (forall a : A -> Prop, (@FINITE A a) = ((a = (@EMPTY A)) \/ (exists x : A, exists s : A -> Prop, (a = (@INSERT A x s)) /\ (@FINITE A s))))).
