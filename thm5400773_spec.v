Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5400773 : forall {A : Type'} (x : A), (~ (@IN A x (@EMPTY A))) -> (@IN A x (@EMPTY A)) = False.