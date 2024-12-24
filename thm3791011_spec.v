Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3791011 : forall {A B : Type'} (f : A -> B -> B) (s : A -> Prop) (a : B) (b : B), (@FINREC A B f b s a (NUMERAL 0)) = ((s = (@EMPTY A)) /\ (a = b)).
