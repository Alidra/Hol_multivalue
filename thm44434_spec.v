Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem44434 : forall {A B : Type'} (r : A -> B -> Prop), (exists a : A, exists b : B, r = (@mk_pair A B a b)) = ((@REP_prod A B (@ABS_prod A B r)) = r).
