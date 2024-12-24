Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306888_term_abbrevs.
Require Import thm2306855_spec.
Require Import thm2306887_spec.
Lemma lem2306888 : term0.
Proof. exact (conj (@lem2306887) (@lem2306855)). Qed.
