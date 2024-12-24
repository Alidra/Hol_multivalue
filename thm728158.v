Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm728158_term_abbrevs.
Require Import thm728073_spec.
Require Import thm728074_spec.
Require Import thm728077_spec.
Require Import thm728078_spec.
Lemma lem728151 (n : nat) : (term0 n) = (term1 n).
Proof. exact (EQ_MP (@lem728074 n) (@lem728073 n)). Qed.
Lemma lem728152 : term2 = term3.
Proof. exact (@lem728151 term4). Qed.
Lemma lem728154 (n : nat) : (term5 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem728078 n) (@lem728077 n)). Qed.
Lemma lem728155 : term6 = term7.
Proof. exact (@lem728154 (BIT1 0)). Qed.
Lemma lem728156 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem728157 : term3 = term8.
Proof. exact (MK_COMB (@lem728156) (@lem728155)). Qed.
Lemma lem728158 : term2 = term8.
Proof. exact (TRANS (@lem728152) (@lem728157)). Qed.
