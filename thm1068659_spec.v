Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1068659 : forall {A B : Type'}, (fun OUTR' : (prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B => forall _17488 : prod nat (prod nat (prod nat nat)), forall y : B, (OUTR' _17488 (@inr A B y)) = y) (@ε ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B) (fun OUTR' : (prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B => forall _17488 : prod nat (prod nat (prod nat nat)), forall y : B, (OUTR' _17488 (@inr A B y)) = y)).
