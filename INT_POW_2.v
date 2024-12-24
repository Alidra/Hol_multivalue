Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_2_term_abbrevs.
Require Import REAL_POW_2_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307723 (x : int) : term0 x.
Proof. exact (@lem1383497 (real_of_int x)). Qed.
Lemma lem2307724 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2307725 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2307724 x) (@lem2307723 x)). Qed.
Lemma lem2307727 (x : int) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307728 (x : int) : (term1 x) = (term5 x).
Proof. exact (@lem2307727 x term6). Qed.
Lemma lem2307729 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307730 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2307729) (@lem2307728 x)). Qed.
Lemma lem2307732 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2307733 (x : int) : (term2 x) = (term11 x).
Proof. exact (@lem2307732 x x). Qed.
Lemma lem2307734 (x : int) : ((term1 x) = (term2 x)) = ((term5 x) = (term11 x)).
Proof. exact (MK_COMB (@lem2307730 x) (@lem2307733 x)). Qed.
Lemma lem2307736 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307737 (x : int) : ((term5 x) = (term11 x)) = ((term12 x) = (int_mul x x)).
Proof. exact (@lem2307736 (term12 x) (int_mul x x)). Qed.
Lemma lem2307738 (x : int) : ((term1 x) = (term2 x)) = ((term12 x) = (int_mul x x)).
Proof. exact (TRANS (@lem2307734 x) (@lem2307737 x)). Qed.
Lemma lem2307739 (x : int) : (term12 x) = (int_mul x x).
Proof. exact (EQ_MP (@lem2307738 x) (@lem2307725 x)). Qed.
Lemma lem2307740 : term13.
Proof. exact (fun x : int => @lem2307739 x). Qed.
