Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066568 : forall {A : Type'} (a : A) (f : nat -> A), (fun f' : nat -> A => (@FCONS A a f' (NUMERAL 0)) = a) f.
