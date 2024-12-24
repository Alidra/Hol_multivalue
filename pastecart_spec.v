Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7632649 : forall {A M N : Type'}, forall f : cart A M, forall g : cart A N, (@pastecart A M N f g) = (@lambda A (finite_sum M N) (fun i : nat => @COND A (Peano.le i (@dimindex M (@UNIV M))) (@dollar A M f i) (@dollar A N g (Nat.sub i (@dimindex M (@UNIV M)))))).
