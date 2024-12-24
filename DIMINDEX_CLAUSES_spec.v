Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7933204 : forall {A : Type'}, ((@dimindex unit (@UNIV unit)) = (NUMERAL (BIT1 0))) /\ (((@dimindex (tybit0 A) (@UNIV (tybit0 A))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex A (@UNIV A)))) /\ ((@dimindex (tybit1 A) (@UNIV (tybit1 A))) = (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex A (@UNIV A))) (NUMERAL (BIT1 0))))).
