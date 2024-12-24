Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7635254 : forall {A M N : Type'}, forall f : cart A (finite_sum M N), (@sndcart A M N f) = (@lambda A N (fun i : nat => @dollar A (finite_sum M N) f (Nat.add i (@dimindex M (@UNIV M))))).
