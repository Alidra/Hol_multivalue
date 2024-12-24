Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm737721_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem737657 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem737658 : term1.
Proof. exact (proj2 (@lem737657)). Qed.
Lemma lem737659 : term2.
Proof. exact (proj2 (@lem737658)). Qed.
Lemma lem737660 : term3.
Proof. exact (proj2 (@lem737659)). Qed.
Lemma lem737661 : term4.
Proof. exact (proj2 (@lem737660)). Qed.
Lemma lem737693 : term5.
Proof. exact (proj1 (@lem737661)). Qed.
Lemma lem737694 (n : nat) : term6 n.
Proof. exact (@lem737693 n). Qed.
Lemma lem737695 (n : nat) : (term6 n) = ((term7 n) = (BIT1 n)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem737718 (n : nat) : (term7 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem737695 n) (@lem737694 n)). Qed.
Lemma lem737719 : term8 = term9.
Proof. exact (@lem737718 term10). Qed.
Lemma lem737720 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem737721 : term11 = term12.
Proof. exact (MK_COMB (@lem737720) (@lem737719)). Qed.
