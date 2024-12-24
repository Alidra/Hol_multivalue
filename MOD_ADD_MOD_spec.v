Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem209995 : forall a : nat, forall b : nat, forall n : nat, (Nat.modulo (Nat.add (Nat.modulo a n) (Nat.modulo b n)) n) = (Nat.modulo (Nat.add a b) n).
