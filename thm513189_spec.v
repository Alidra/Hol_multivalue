Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem513189 : forall (n : nat), (fun n' : nat => (NUMERAL n') = n') n.
