Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7990967 : forall {A N : Type'}, forall m : nat, (@HAS_SIZE A (@UNIV A) m) -> @HAS_SIZE (cart A N) (@UNIV (cart A N)) (Nat.pow m (@dimindex N (@UNIV N))).
