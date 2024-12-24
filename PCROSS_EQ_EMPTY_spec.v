Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8005884 : forall {_141954 _141955 _141956 : Type'}, forall s : (cart _141954 _141955) -> Prop, forall t : (cart _141954 _141956) -> Prop, ((@PCROSS _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = ((s = (@EMPTY (cart _141954 _141955))) \/ (t = (@EMPTY (cart _141954 _141956)))).
