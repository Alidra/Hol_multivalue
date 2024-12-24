Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7640378 : forall {M N : Type'}, @HAS_SIZE (finite_sum M N) (@IMAGE nat (finite_sum M N) (@mk_finite_sum M N) (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N))))) (Nat.add (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N))).
