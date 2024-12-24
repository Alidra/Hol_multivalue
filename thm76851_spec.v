Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem76851 : Nat.pred = (@ε ((prod nat (prod nat nat)) -> nat -> nat) (fun PRE' : (prod nat (prod nat nat)) -> nat -> nat => forall _2151 : prod nat (prod nat nat), ((PRE' _2151 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall n : nat, (PRE' _2151 (S n)) = n)) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))).
