Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400781_term_abbrevs.
Require Import IN_NUMSEG_spec.
Lemma lem5400775 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5400776 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5400777 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5400776 m) (@lem5400775 m)). Qed.
Lemma lem5400778 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem5400777 m n). Qed.
Lemma lem5400779 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem5400780 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem5400779 m n) (@lem5400778 m n)). Qed.
Lemma lem5400781 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem5400780 m n p). Qed.
