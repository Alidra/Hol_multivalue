Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1203021 : forall {_28101 : Type'}, forall p : list _28101, forall q : list _28101, (@LAST _28101 (@List.app _28101 p q)) = (@COND _28101 (q = (@nil _28101)) (@LAST _28101 p) (@LAST _28101 q)).
