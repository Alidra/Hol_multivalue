Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8003767 : forall {A M N : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N) -> Prop, (@PCROSS A M N s t) = (@GSPEC (cart A (finite_sum M N)) (fun GEN_PVAR_361 : cart A (finite_sum M N) => exists x : cart A M, exists y : cart A N, @SETSPEC (cart A (finite_sum M N)) GEN_PVAR_361 ((@IN (cart A M) x s) /\ (@IN (cart A N) y t)) (@pastecart A M N x y))).
