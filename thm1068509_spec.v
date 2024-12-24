Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1068509 : forall {A B : Type'}, (@OUTL A B) = (@ε ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A) (fun OUTL' : (prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A => forall _17486 : prod nat (prod nat (prod nat nat)), forall x : A, (OUTL' _17486 (@inl A B x)) = x) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))).
