Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7614824 : forall {N : Type'} (P : (finite_image N) -> Prop), (forall k : finite_image N, P k) = (forall i : nat, ((Peano.le (NUMERAL (BIT1 0)) i) /\ (Peano.le i (@dimindex N (@UNIV N)))) -> P (@finite_index N i)).
