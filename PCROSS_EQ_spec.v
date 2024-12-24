Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8026003 : forall {M N : Type'}, forall s : (cart real M) -> Prop, forall s' : (cart real M) -> Prop, forall t : (cart real N) -> Prop, forall t' : (cart real N) -> Prop, ((@PCROSS real M N s t) = (@PCROSS real M N s' t')) = ((((s = (@EMPTY (cart real M))) \/ (t = (@EMPTY (cart real N)))) /\ ((s' = (@EMPTY (cart real M))) \/ (t' = (@EMPTY (cart real N))))) \/ ((s = s') /\ (t = t'))).
