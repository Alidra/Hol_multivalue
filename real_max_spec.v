Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1345564 : forall n : real, forall m : real, (real_max m n) = (@COND real (real_le m n) n m).
