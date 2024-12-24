Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066553 : forall {A : Type'}, forall n : nat, (@FNIL A n) = (@ε A (fun x : A => True)).
