Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_1_term_abbrevs.
Require Import REAL_POW_1_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307611 (x : int) : term0 x.
Proof. exact (@lem1631005 (real_of_int x)). Qed.
Lemma lem2307612 (x : int) : (term0 x) = ((term1 x) = (real_of_int x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2307613 (x : int) : (term1 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2307612 x) (@lem2307611 x)). Qed.
Lemma lem2307615 (x : int) (n : nat) : (term2 x n) = (term3 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307616 (x : int) : (term1 x) = (term4 x).
Proof. exact (@lem2307615 x term5). Qed.
Lemma lem2307617 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307618 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2307617) (@lem2307616 x)). Qed.
Lemma lem2307619 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2307620 (x : int) : ((term1 x) = (real_of_int x)) = ((term4 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2307618 x) (@lem2307619 x)). Qed.
Lemma lem2307622 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307623 (x : int) : ((term4 x) = (real_of_int x)) = ((term8 x) = x).
Proof. exact (@lem2307622 (term8 x) x). Qed.
Lemma lem2307624 (x : int) : ((term1 x) = (real_of_int x)) = ((term8 x) = x).
Proof. exact (TRANS (@lem2307620 x) (@lem2307623 x)). Qed.
Lemma lem2307625 (x : int) : (term8 x) = x.
Proof. exact (EQ_MP (@lem2307624 x) (@lem2307613 x)). Qed.
Lemma lem2307626 : term9.
Proof. exact (fun x : int => @lem2307625 x). Qed.
