Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_CLAUSES_term_abbrevs.
Require Import thm5418314_spec.
Require Import thm5418324_spec.
Lemma lem5418329 : term0.
Proof. exact (fun m : nat => @lem5418314 m). Qed.
Lemma lem5418330 : term1.
Proof. exact (conj (@lem5418329) (@lem5418324)). Qed.
