Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066033 : forall {A : Type'}, (@FCONS A) = (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A) (fun FCONS' : (prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A => forall _17460 : prod nat (prod nat (prod nat (prod nat nat))), (forall a : A, forall f : nat -> A, (FCONS' _17460 a f (NUMERAL 0)) = a) /\ (forall a : A, forall f : nat -> A, forall n : nat, (FCONS' _17460 a f (S n)) = (f n))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))).
