Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1268738 : forall k : nat, (nadd_of_num k) = (mk_nadd (fun n : nat => Nat.mul k n)).
