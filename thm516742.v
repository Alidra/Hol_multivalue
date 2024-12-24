Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516742_term_abbrevs.
Require Import LT_MULT_LCANCEL_spec.
Lemma lem516736 (m : nat) : term0 m.
Proof. exact (@lem105882 m). Qed.
Lemma lem516737 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem516738 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem516737 m) (@lem516736 m)). Qed.
Lemma lem516739 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem516738 m n). Qed.
Lemma lem516740 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem516741 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem516740 m n) (@lem516739 m n)). Qed.
Lemma lem516742 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem516741 m n p). Qed.
