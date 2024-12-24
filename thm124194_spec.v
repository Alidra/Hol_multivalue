Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem124194 : Coq.Arith.PeanoNat.Nat.Even = (@ε ((prod nat (prod nat (prod nat nat))) -> nat -> Prop) (fun EVEN' : (prod nat (prod nat (prod nat nat))) -> nat -> Prop => forall _2603 : prod nat (prod nat (prod nat nat)), ((EVEN' _2603 (NUMERAL 0)) = True) /\ (forall n : nat, (EVEN' _2603 (S n)) = (~ (EVEN' _2603 n)))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))).
