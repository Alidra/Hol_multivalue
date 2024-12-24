Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248935_term_abbrevs.
Lemma lem1248935 (d : nat) (d' : nat) (d'' : nat) (h1 : term0 d d' d'') : term0 d d' d''.
Proof. exact (h1). Qed.
