Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1244859 : forall n : nat, (dist (@pair nat nat (NUMERAL 0) n)) = n.
