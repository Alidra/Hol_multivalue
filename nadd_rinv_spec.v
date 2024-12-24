Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1300973 : forall x : nadd, (nadd_rinv x) = (fun n : nat => Nat.div (Nat.mul n n) (dest_nadd x n)).
