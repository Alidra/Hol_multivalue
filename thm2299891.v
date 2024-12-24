Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299891_term_abbrevs.
Require Import thm2299824_spec.
Lemma lem2299891 (x : int) : term0 x.
Proof. exact (@lem2299824 x). Qed.
