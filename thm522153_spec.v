Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522153 : forall (m : nat) (n : nat), (fun n' : nat => ((Nat.sub m n') = 0) = (Peano.le m n')) n.
