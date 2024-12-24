Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418319_term_abbrevs.
Require Import thm5418304_spec.
Lemma lem5418319 (m : nat) : term0 m.
Proof. exact (fun n : nat => @lem5418304 m n). Qed.
