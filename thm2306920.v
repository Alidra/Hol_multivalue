Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306920_term_abbrevs.
Require Import thm2306919_spec.
Lemma lem2306920 : term0.
Proof. exact (fun m : nat => @lem2306919 m). Qed.