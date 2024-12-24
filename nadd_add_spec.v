Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1273759 : forall x : nadd, forall y : nadd, (nadd_add x y) = (mk_nadd (fun n : nat => Nat.add (dest_nadd x n) (dest_nadd y n))).
