Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515685_term_abbrevs.
Require Import thm515633_spec.
Lemma lem515684 : term0.
Proof. exact (proj1 (@lem515633)). Qed.
Lemma lem515685 (m : nat) : term1 m.
Proof. exact (@lem515684 m). Qed.
