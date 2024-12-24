Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066569 : forall {A : Type'} (f : nat -> A) (a : A), ((fun f' : nat -> A => (@FCONS A a f' (NUMERAL 0)) = a) f) = ((@FCONS A a f (NUMERAL 0)) = a).
