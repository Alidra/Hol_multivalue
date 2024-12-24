Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1065718 : forall {A : Type'}, (fun FCONS' : (prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A => forall _17460 : prod nat (prod nat (prod nat (prod nat nat))), (forall a : A, forall f : nat -> A, (FCONS' _17460 a f (NUMERAL 0)) = a) /\ (forall a : A, forall f : nat -> A, forall n : nat, (FCONS' _17460 a f (S n)) = (f n))) (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A) (fun FCONS' : (prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A => forall _17460 : prod nat (prod nat (prod nat (prod nat nat))), (forall a : A, forall f : nat -> A, (FCONS' _17460 a f (NUMERAL 0)) = a) /\ (forall a : A, forall f : nat -> A, forall n : nat, (FCONS' _17460 a f (S n)) = (f n)))).
