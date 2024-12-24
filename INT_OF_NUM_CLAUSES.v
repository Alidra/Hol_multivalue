Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_CLAUSES_term_abbrevs.
Require Import thm2307095_spec.
Require Import thm2307120_spec.
Lemma lem2307121 : term0.
Proof. exact (fun m : nat => @lem2307120 m). Qed.
Lemma lem2307122 : term1.
Proof. exact (conj (@lem2307121) (@lem2307095)). Qed.
