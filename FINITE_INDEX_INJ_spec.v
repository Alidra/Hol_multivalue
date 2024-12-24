Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7612100 : forall {A : Type'}, forall i : nat, forall j : nat, ((Peano.le (NUMERAL (BIT1 0)) i) /\ ((Peano.le i (@dimindex A (@UNIV A))) /\ ((Peano.le (NUMERAL (BIT1 0)) j) /\ (Peano.le j (@dimindex A (@UNIV A)))))) -> ((@finite_index A i) = (@finite_index A j)) = (i = j).
