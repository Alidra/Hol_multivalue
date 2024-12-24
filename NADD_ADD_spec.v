Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1274104 : forall x : nadd, forall y : nadd, (dest_nadd (nadd_add x y)) = (fun n : nat => Nat.add (dest_nadd x n) (dest_nadd y n)).
