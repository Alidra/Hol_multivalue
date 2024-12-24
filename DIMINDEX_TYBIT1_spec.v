Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7933119 : forall {A : Type'}, (@dimindex (tybit1 A) (@UNIV (tybit1 A))) = (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex A (@UNIV A))) (NUMERAL (BIT1 0))).
