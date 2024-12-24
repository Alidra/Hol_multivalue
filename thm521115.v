Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm521115_term_abbrevs.
Require Import LTE_ANTISYM_spec.
Lemma lem521110 (m : nat) : term0 m.
Proof. exact (@lem93080 m). Qed.
Lemma lem521111 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem521112 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem521111 m) (@lem521110 m)). Qed.
Lemma lem521113 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem521112 m n). Qed.
Lemma lem521114 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem521115 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem521114 n m) (@lem521113 m n)). Qed.
