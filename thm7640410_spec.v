Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7640410 : forall {M N : Type'}, ((@COND nat (@FINITE (finite_sum M N) (@UNIV (finite_sum M N))) (@CARD (finite_sum M N) (@UNIV (finite_sum M N))) (NUMERAL (BIT1 0))) = (Nat.add (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N)))) = ((@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (Nat.add (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N)))).
