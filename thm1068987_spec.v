Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1068987 : forall {A B : Type'}, (@OUTR A B) = (@ε ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B) (fun OUTR' : (prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B => forall _17488 : prod nat (prod nat (prod nat nat)), forall y : B, (OUTR' _17488 (@inr A B y)) = y) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).
