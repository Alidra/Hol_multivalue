Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7921508 : forall {A B : Type'}, (@UNIV (finite_prod A B)) = (@IMAGE nat (finite_prod A B) (@mk_finite_prod A B) (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))).
