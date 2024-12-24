Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306887_term_abbrevs.
Require Import thm2306886_spec.
Lemma lem2306887 : term0.
Proof. exact (fun m : nat => @lem2306886 m). Qed.
