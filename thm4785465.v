Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4785465_term_abbrevs.
Require Import thm4785464_spec.
Lemma lem4785465 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem4785464 A)). Qed.