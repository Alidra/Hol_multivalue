Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522189_term_abbrevs.
Require Import SUB_SUC_spec.
Lemma lem522186 (m : nat) : term0 m.
Proof. exact (@lem135645 m). Qed.
Lemma lem522187 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem522188 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem522187 m) (@lem522186 m)). Qed.
Lemma lem522189 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem522188 m n). Qed.
