Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7622314 : forall {A B : Type'} (g : nat -> A), forall i : nat, ((Peano.le (NUMERAL (BIT1 0)) i) /\ (Peano.le i (@dimindex B (@UNIV B)))) -> (@dollar A B (@lambda A B g) i) = (g i).
