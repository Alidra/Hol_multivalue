Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem135024 : Nat.sub = (@ε (nat -> nat -> nat -> nat) (fun minus' : nat -> nat -> nat -> nat => forall _2766 : nat, (forall m : nat, (minus' _2766 m (NUMERAL 0)) = m) /\ (forall m : nat, forall n : nat, (minus' _2766 m (S n)) = (Nat.pred (minus' _2766 m n)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))).
