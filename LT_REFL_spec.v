Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem91686 : forall n : nat, ~ (Peano.lt n n).
