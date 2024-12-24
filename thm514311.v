Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm514311_term_abbrevs.
Require Import LEFT_ADD_DISTRIB_spec.
Lemma lem514305 (m : nat) : term0 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem514306 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem514307 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem514306 m) (@lem514305 m)). Qed.
Lemma lem514308 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem514307 m n). Qed.
Lemma lem514309 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem514310 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem514309 n m) (@lem514308 m n)). Qed.
Lemma lem514311 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem514310 n m p). Qed.
