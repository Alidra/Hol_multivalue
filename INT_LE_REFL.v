Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_REFL_term_abbrevs.
Require Import thm1339240_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303150 (x : int) : term0 x.
Proof. exact (@lem1339240 (real_of_int x)). Qed.
Lemma lem2303151 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303152 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303151 x) (@lem2303150 x)). Qed.
Lemma lem2303154 (x : int) (y : int) : (term2 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303155 (x : int) : (term1 x) = (int_le x x).
Proof. exact (@lem2303154 x x). Qed.
Lemma lem2303156 (x : int) : int_le x x.
Proof. exact (EQ_MP (@lem2303155 x) (@lem2303152 x)). Qed.
Lemma lem2303157 : term3.
Proof. exact (fun x : int => @lem2303156 x). Qed.
