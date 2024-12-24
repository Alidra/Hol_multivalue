Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8036724 : forall {M N : Type'}, forall s : (cart real M) -> Prop, forall t : (cart real N) -> Prop, (@IMAGE (cart real (finite_sum M N)) (cart real N) (@sndcart real M N) (@PCROSS real M N s t)) = (@COND ((cart real N) -> Prop) (s = (@EMPTY (cart real M))) (@EMPTY (cart real N)) t).
