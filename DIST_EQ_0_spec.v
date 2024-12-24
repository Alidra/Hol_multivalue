Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1245573 : forall m : nat, forall n : nat, ((dist (@pair nat nat m n)) = (NUMERAL 0)) = (m = n).
