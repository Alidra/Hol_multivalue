Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7618353 : forall {A B : Type'}, forall g : nat -> A, (@lambda A B g) = (@ε (cart A B) (fun f : cart A B => forall i : nat, ((Peano.le (NUMERAL (BIT1 0)) i) /\ (Peano.le i (@dimindex B (@UNIV B)))) -> (@dollar A B f i) = (g i))).
