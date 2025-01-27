Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7624600 : forall {A B : Type'}, forall f : cart A B, forall g : nat -> A, (forall i : nat, ((Peano.le (NUMERAL (BIT1 0)) i) /\ (Peano.le i (@dimindex B (@UNIV B)))) -> (@dollar A B f i) = (g i)) = ((@lambda A B g) = f).
