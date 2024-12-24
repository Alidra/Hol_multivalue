Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7999996 : forall {A N : Type'}, (@FINITE A (@UNIV A)) -> @FINITE (cart A N) (@UNIV (cart A N)).
