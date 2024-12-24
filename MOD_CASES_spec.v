Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem177172 : forall n : nat, forall p : nat, (Peano.lt n (Nat.mul (NUMERAL (BIT0 (BIT1 0))) p)) -> (Nat.modulo n p) = (@COND nat (Peano.lt n p) n (Nat.sub n p)).
