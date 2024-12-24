Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm728149_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem728085 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem728086 : term1.
Proof. exact (proj2 (@lem728085)). Qed.
Lemma lem728087 : term2.
Proof. exact (proj2 (@lem728086)). Qed.
Lemma lem728088 : term3.
Proof. exact (proj2 (@lem728087)). Qed.
Lemma lem728089 : term4.
Proof. exact (proj2 (@lem728088)). Qed.
Lemma lem728121 : term5.
Proof. exact (proj1 (@lem728089)). Qed.
Lemma lem728122 (n : nat) : term6 n.
Proof. exact (@lem728121 n). Qed.
Lemma lem728123 (n : nat) : (term6 n) = ((term7 n) = (BIT1 n)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem728146 (n : nat) : (term7 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem728123 n) (@lem728122 n)). Qed.
Lemma lem728147 : term8 = term9.
Proof. exact (@lem728146 term10). Qed.
Lemma lem728148 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem728149 : term11 = term12.
Proof. exact (MK_COMB (@lem728148) (@lem728147)). Qed.
