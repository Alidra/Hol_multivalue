Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7603578 : forall {A : Type'}, (forall x : finite_image A, exists x' : nat, (x = (@finite_index A x')) /\ (@IN nat x' (dotdot (NUMERAL (BIT1 0)) (@dimindex A (@UNIV A))))) = ((@UNIV (finite_image A)) = (@IMAGE nat (finite_image A) (@finite_index A) (dotdot (NUMERAL (BIT1 0)) (@dimindex A (@UNIV A))))).
