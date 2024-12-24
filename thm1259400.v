Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259400_term_abbrevs.
Require Import thm1248614_spec.
Require Import thm1259364_spec.
Lemma lem1259400 (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : p = (term0 p d d' d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248614 d d' d'') (@lem1259364 p d d' d'' h1)). Qed.
