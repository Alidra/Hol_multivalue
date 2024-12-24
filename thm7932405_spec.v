Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7932405 : forall {A : Type'} (h1 : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))), (@HAS_SIZE (tybit1 A) (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex A (@UNIV A))) (NUMERAL (BIT1 0)))) = (@HAS_SIZE (tybit1 A) (@UNIV (tybit1 A)) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex A (@UNIV A))) (NUMERAL (BIT1 0)))).
