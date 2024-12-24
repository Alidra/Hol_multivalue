Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7637130 : forall {A B : Type'}, (@UNIV (finite_sum A B)) = (@IMAGE nat (finite_sum A B) (@mk_finite_sum A B) (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))).
