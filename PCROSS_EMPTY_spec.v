Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8005965 : forall {_141980 _141981 _141982 _141994 _141995 _141996 : Type'}, (forall s : (cart _141980 _141981) -> Prop, (@PCROSS _141980 _141981 _141982 s (@EMPTY (cart _141980 _141982))) = (@EMPTY (cart _141980 (finite_sum _141981 _141982)))) /\ (forall t : (cart _141994 _141996) -> Prop, (@PCROSS _141994 _141995 _141996 (@EMPTY (cart _141994 _141995)) t) = (@EMPTY (cart _141994 (finite_sum _141995 _141996)))).
