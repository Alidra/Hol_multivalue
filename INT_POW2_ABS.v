Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW2_ABS_term_abbrevs.
Require Import REAL_POW2_ABS_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307586 (x : int) : term0 x.
Proof. exact (@lem1643626 (real_of_int x)). Qed.
Lemma lem2307587 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2307588 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2307587 x) (@lem2307586 x)). Qed.
Lemma lem2307590 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2307591 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2307592 (x : int) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem2307591) (@lem2307590 x)). Qed.
Lemma lem2307593 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem2307594 (x : int) : (term1 x) = (term8 x).
Proof. exact (MK_COMB (@lem2307592 x) (@lem2307593)). Qed.
Lemma lem2307596 (x : int) (n : nat) : (term9 x n) = (term10 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307597 (x : int) : (term8 x) = (term11 x).
Proof. exact (@lem2307596 (int_abs x) term7). Qed.
Lemma lem2307598 (x : int) : (term1 x) = (term11 x).
Proof. exact (TRANS (@lem2307594 x) (@lem2307597 x)). Qed.
Lemma lem2307599 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307600 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2307599) (@lem2307598 x)). Qed.
Lemma lem2307602 (x : int) (n : nat) : (term9 x n) = (term10 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307603 (x : int) : (term2 x) = (term14 x).
Proof. exact (@lem2307602 x term7). Qed.
Lemma lem2307604 (x : int) : ((term1 x) = (term2 x)) = ((term11 x) = (term14 x)).
Proof. exact (MK_COMB (@lem2307600 x) (@lem2307603 x)). Qed.
Lemma lem2307606 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307607 (x : int) : ((term11 x) = (term14 x)) = ((term15 x) = (term16 x)).
Proof. exact (@lem2307606 (term15 x) (term16 x)). Qed.
Lemma lem2307608 (x : int) : ((term1 x) = (term2 x)) = ((term15 x) = (term16 x)).
Proof. exact (TRANS (@lem2307604 x) (@lem2307607 x)). Qed.
Lemma lem2307609 (x : int) : (term15 x) = (term16 x).
Proof. exact (EQ_MP (@lem2307608 x) (@lem2307588 x)). Qed.
Lemma lem2307610 : term17.
Proof. exact (fun x : int => @lem2307609 x). Qed.
