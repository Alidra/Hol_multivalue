Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7924816 : forall {M N : Type'}, (@dimindex (finite_prod M N) (@UNIV (finite_prod M N))) = (Nat.mul (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N))).
