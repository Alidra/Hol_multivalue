Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8027156 : forall {A M N : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N) -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE (cart A M) s m) /\ (@HAS_SIZE (cart A N) t n)) -> @HAS_SIZE (cart A (finite_sum M N)) (@PCROSS A M N s t) (Nat.mul m n).
