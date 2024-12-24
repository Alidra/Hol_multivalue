Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516842_term_abbrevs.
Require Import SUC_INJ_spec.
Lemma lem516839 (m : nat) : term0 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem516840 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem516841 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem516840 m) (@lem516839 m)). Qed.
Lemma lem516842 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem516841 m n). Qed.
