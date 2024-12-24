Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1268972 : forall k : nat, (dest_nadd (nadd_of_num k)) = (fun n : nat => Nat.mul k n).
