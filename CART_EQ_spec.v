Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7617066 : forall {A B : Type'}, forall x : cart A B, forall y : cart A B, (x = y) = (forall i : nat, ((Peano.le (NUMERAL (BIT1 0)) i) /\ (Peano.le i (@dimindex B (@UNIV B)))) -> (@dollar A B x i) = (@dollar A B y i)).
