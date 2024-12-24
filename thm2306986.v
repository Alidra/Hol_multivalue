Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306986_term_abbrevs.
Require Import thm2306985_spec.
Lemma lem2306986 : term0.
Proof. exact (fun m : nat => @lem2306985 m). Qed.
