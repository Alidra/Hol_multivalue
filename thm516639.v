Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516639_term_abbrevs.
Require Import NOT_SUC_spec.
Lemma lem516637 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem516638 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem516639 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem516638 n) (@lem516637 n)). Qed.
