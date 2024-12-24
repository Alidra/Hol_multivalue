Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7933103 : forall {A : Type'}, (@dimindex (tybit0 A) (@UNIV (tybit0 A))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex A (@UNIV A))).
