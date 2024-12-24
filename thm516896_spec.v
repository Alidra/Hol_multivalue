Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516896 : forall (m : nat), (fun m' : nat => (Peano.le m' 0) = (m' = 0)) m.
