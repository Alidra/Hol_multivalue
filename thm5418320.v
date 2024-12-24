Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418320_term_abbrevs.
Require Import thm5418319_spec.
Lemma lem5418320 : term0.
Proof. exact (fun m : nat => @lem5418319 m). Qed.
