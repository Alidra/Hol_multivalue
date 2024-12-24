Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm709122_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem709058 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem709059 : term1.
Proof. exact (proj2 (@lem709058)). Qed.
Lemma lem709106 : term2.
Proof. exact (proj1 (@lem709059)). Qed.
Lemma lem709107 (n : nat) : term3 n.
Proof. exact (@lem709106 n). Qed.
Lemma lem709108 (n : nat) : (term3 n) = ((term4 n) = (BIT0 n)).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem709119 (n : nat) : (term4 n) = (BIT0 n).
Proof. exact (EQ_MP (@lem709108 n) (@lem709107 n)). Qed.
Lemma lem709120 : term5 = term6.
Proof. exact (@lem709119 (BIT1 0)). Qed.
Lemma lem709121 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem709122 : term7 = term8.
Proof. exact (MK_COMB (@lem709121) (@lem709120)). Qed.
