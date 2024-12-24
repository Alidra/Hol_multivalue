Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3197567 : forall {A : Type'}, forall FINITE' : (A -> Prop) -> Prop, ((FINITE' (@EMPTY A)) /\ (forall x : A, forall s : A -> Prop, (FINITE' s) -> FINITE' (@INSERT A x s))) -> forall a : A -> Prop, (@FINITE A a) -> FINITE' a.
