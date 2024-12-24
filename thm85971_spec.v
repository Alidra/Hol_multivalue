Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem85971 : (fun EXP' : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _2224 : prod nat (prod nat nat), (forall m : nat, (EXP' _2224 m (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall m : nat, forall n : nat, (EXP' _2224 m (S n)) = (Nat.mul m (EXP' _2224 m n)))) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun EXP' : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _2224 : prod nat (prod nat nat), (forall m : nat, (EXP' _2224 m (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall m : nat, forall n : nat, (EXP' _2224 m (S n)) = (Nat.mul m (EXP' _2224 m n))))).
