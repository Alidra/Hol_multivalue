Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1068536 : forall {A B : Type'} (x : A), (@OUTL A B (@inl A B x)) = x.
