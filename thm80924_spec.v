Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem80924 : Nat.mul = (@ε (nat -> nat -> nat -> nat) (fun mul' : nat -> nat -> nat -> nat => forall _2186 : nat, (forall n : nat, (mul' _2186 (NUMERAL 0) n) = (NUMERAL 0)) /\ (forall m : nat, forall n : nat, (mul' _2186 (S m) n) = (Nat.add (mul' _2186 m n) n))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))).
