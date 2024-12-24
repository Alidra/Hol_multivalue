Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528090_term_abbrevs.
Require Import thm528004_spec.
Require Import thm528019_spec.
Lemma lem528083 : (Nat.add 0 0) = 0.
Proof. exact (proj1 (@lem528019)). Qed.
Lemma lem528084 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem528085 : term0 = (S 0).
Proof. exact (MK_COMB (@lem528084) (@lem528083)). Qed.
Lemma lem528087 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem528004)). Qed.
Lemma lem528088 : term0 = (BIT1 0).
Proof. exact (TRANS (@lem528085) (@lem528087)). Qed.
Lemma lem528089 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem528090 : term1 = term2.
Proof. exact (MK_COMB (@lem528089) (@lem528088)). Qed.
