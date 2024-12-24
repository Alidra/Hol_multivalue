Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7996376 : forall {A N : Type'}, (@FINITE A (@UNIV A)) -> (@CARD (cart A N) (@UNIV (cart A N))) = (Nat.pow (@CARD A (@UNIV A)) (@dimindex N (@UNIV N))).
