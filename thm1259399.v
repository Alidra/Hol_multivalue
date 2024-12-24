Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259399_term_abbrevs.
Require Import thm1248630_spec.
Require Import thm1259359_spec.
Lemma lem1259399 (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : n = (term0 n d' d d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248630 d d' d'') (@lem1259359 n d' d d'' h1)). Qed.
