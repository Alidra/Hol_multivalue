Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8035216 : forall {M N : Type'}, forall s : (cart real M) -> Prop, forall t : (cart real N) -> Prop, (@IMAGE (cart real (finite_sum M N)) (cart real M) (@fstcart real M N) (@PCROSS real M N s t)) = (@COND ((cart real M) -> Prop) (t = (@EMPTY (cart real N))) (@EMPTY (cart real M)) s).
