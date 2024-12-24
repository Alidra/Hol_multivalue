Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1346200 : forall m : real, forall n : real, (real_min m n) = (@COND real (real_le m n) m n).
