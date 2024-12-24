Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1337531 : forall (m : nat), (real_of_num m) = (mk_real (treal_eq (treal_of_num m))).
