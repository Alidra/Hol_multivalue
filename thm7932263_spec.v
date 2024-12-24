Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7932263 : forall {A : Type'}, ((@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))) = (@HAS_SIZE (tybit0 A) (@UNIV (tybit0 A)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex A (@UNIV A)))).
