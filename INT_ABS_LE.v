Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_LE_term_abbrevs.
Require Import REAL_ABS_LE_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2300382 (x : int) : term0 x.
Proof. exact (@lem1535817 (real_of_int x)). Qed.
Lemma lem2300383 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300384 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300383 x) (@lem2300382 x)). Qed.
Lemma lem2300386 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300387 (x : int) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem2300388 (x : int) : (term1 x) = (term5 x).
Proof. exact (MK_COMB (@lem2300387 x) (@lem2300386 x)). Qed.
Lemma lem2300390 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2300391 (x : int) : (term5 x) = (term7 x).
Proof. exact (@lem2300390 x (int_abs x)). Qed.
Lemma lem2300392 (x : int) : (term1 x) = (term7 x).
Proof. exact (TRANS (@lem2300388 x) (@lem2300391 x)). Qed.
Lemma lem2300393 (x : int) : term7 x.
Proof. exact (EQ_MP (@lem2300392 x) (@lem2300384 x)). Qed.
Lemma lem2300394 : term8.
Proof. exact (fun x : int => @lem2300393 x). Qed.
