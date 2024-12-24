Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7917620 : forall {M N : Type'}, @HAS_SIZE (finite_diff M N) (@UNIV (finite_diff M N)) (@COND nat (Peano.lt (@dimindex N (@UNIV N)) (@dimindex M (@UNIV M))) (Nat.sub (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N))) (NUMERAL (BIT1 0))).
