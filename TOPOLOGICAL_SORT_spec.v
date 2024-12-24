Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5700874 : forall {A : Type'}, forall lt2 : A -> A -> Prop, ((forall x : A, forall y : A, ((lt2 x y) /\ (lt2 y x)) -> x = y) /\ (forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z)) -> forall n : nat, forall s : A -> Prop, (@HAS_SIZE A s n) -> exists f : nat -> A, (s = (@IMAGE nat A f (dotdot (NUMERAL (BIT1 0)) n))) /\ (forall j : nat, forall k : nat, ((@IN nat j (dotdot (NUMERAL (BIT1 0)) n)) /\ ((@IN nat k (dotdot (NUMERAL (BIT1 0)) n)) /\ (Peano.lt j k))) -> ~ (lt2 (f k) (f j))).
