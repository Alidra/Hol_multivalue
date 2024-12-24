Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem136259 : forall m : nat, forall n : nat, ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n).
