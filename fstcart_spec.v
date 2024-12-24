Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7633949 : forall {A M N : Type'}, forall f : cart A (finite_sum M N), (@fstcart A M N f) = (@lambda A M (fun i : nat => @dollar A (finite_sum M N) f i)).
