Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3121565 : forall a : nat, forall n : nat, (num_coprime (@pair nat nat (Nat.modulo a n) n)) = (num_coprime (@pair nat nat a n)).
