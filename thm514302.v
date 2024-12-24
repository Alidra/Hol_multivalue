Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm514302_term_abbrevs.
Require Import RIGHT_ADD_DISTRIB_spec.
Lemma lem514296 (m : nat) : term0 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem514297 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem514298 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem514297 m) (@lem514296 m)). Qed.
Lemma lem514299 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem514298 m n). Qed.
Lemma lem514300 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem514301 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem514300 m n) (@lem514299 m n)). Qed.
Lemma lem514302 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem514301 m n p). Qed.
