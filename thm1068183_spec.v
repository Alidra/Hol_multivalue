Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1068183 : forall {A B : Type'}, (fun OUTL' : (prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A => forall _17486 : prod nat (prod nat (prod nat nat)), forall x : A, (OUTL' _17486 (@inl A B x)) = x) (@ε ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A) (fun OUTL' : (prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A => forall _17486 : prod nat (prod nat (prod nat nat)), forall x : A, (OUTL' _17486 (@inl A B x)) = x)).
