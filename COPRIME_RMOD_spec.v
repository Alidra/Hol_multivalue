Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3123784 : forall a : nat, forall n : nat, (num_coprime (@pair nat nat n (Nat.modulo a n))) = (num_coprime (@pair nat nat n a)).
