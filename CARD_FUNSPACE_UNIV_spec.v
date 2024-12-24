Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4588126 : forall {A B : Type'}, ((@FINITE A (@UNIV A)) /\ (@FINITE B (@UNIV B))) -> (@CARD (A -> B) (@UNIV (A -> B))) = (Nat.pow (@CARD B (@UNIV B)) (@CARD A (@UNIV A))).
