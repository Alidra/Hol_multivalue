Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm759298_term_abbrevs.
Require Import thm759207_spec.
Require Import thm759208_spec.
Require Import thm759211_spec.
Require Import thm759212_spec.
Lemma lem759285 (n : nat) : (term0 n) = (term1 n).
Proof. exact (EQ_MP (@lem759208 n) (@lem759207 n)). Qed.
Lemma lem759286 : term2 = term3.
Proof. exact (@lem759285 term4). Qed.
Lemma lem759288 (n : nat) : (term0 n) = (term1 n).
Proof. exact (EQ_MP (@lem759208 n) (@lem759207 n)). Qed.
Lemma lem759289 : term5 = term6.
Proof. exact (@lem759288 term7). Qed.
Lemma lem759291 (n : nat) : (term8 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem759212 n) (@lem759211 n)). Qed.
Lemma lem759292 : term9 = term10.
Proof. exact (@lem759291 (BIT1 0)). Qed.
Lemma lem759293 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem759294 : term6 = term11.
Proof. exact (MK_COMB (@lem759293) (@lem759292)). Qed.
Lemma lem759295 : term5 = term11.
Proof. exact (TRANS (@lem759289) (@lem759294)). Qed.
Lemma lem759296 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem759297 : term3 = term12.
Proof. exact (MK_COMB (@lem759296) (@lem759295)). Qed.
Lemma lem759298 : term2 = term12.
Proof. exact (TRANS (@lem759286) (@lem759297)). Qed.
