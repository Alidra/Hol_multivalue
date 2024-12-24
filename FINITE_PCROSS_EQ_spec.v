Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8033712 : forall {A M N : Type'}, forall s : (cart A M) -> Prop, forall t : (cart A N) -> Prop, (@FINITE (cart A (finite_sum M N)) (@PCROSS A M N s t)) = ((s = (@EMPTY (cart A M))) \/ ((t = (@EMPTY (cart A N))) \/ ((@FINITE (cart A M) s) /\ (@FINITE (cart A N) t)))).
