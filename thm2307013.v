Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2307013_term_abbrevs.
Require Import thm2307012_spec.
Lemma lem2307013 : term0.
Proof. exact (fun m : nat => @lem2307012 m). Qed.
