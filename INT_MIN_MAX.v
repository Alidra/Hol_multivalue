Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MIN_MAX_term_abbrevs.
Require Import REAL_MIN_MAX_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305698 (x : int) : term0 x.
Proof. exact (@lem1555966 (real_of_int x)). Qed.
Lemma lem2305699 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305700 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305699 x) (@lem2305698 x)). Qed.
Lemma lem2305701 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305700 x (real_of_int y)). Qed.
Lemma lem2305702 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305703 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2305702 x y) (@lem2305701 x y)). Qed.
Lemma lem2305705 (x : int) (y : int) : (term3 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305706 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305707 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2305706) (@lem2305705 x y)). Qed.
Lemma lem2305709 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2305710 : real_max = real_max.
Proof. exact (eq_refl real_max). Qed.
Lemma lem2305711 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2305710) (@lem2305709 x)). Qed.
Lemma lem2305713 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2305714 (y : int) : (term8 y) = (term9 y).
Proof. exact (@lem2305713 y). Qed.
Lemma lem2305715 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2305711 x) (@lem2305714 y)). Qed.
Lemma lem2305717 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305718 (x : int) (y : int) : (term13 x y) = (term16 x y).
Proof. exact (@lem2305717 (int_neg x) (int_neg y)). Qed.
Lemma lem2305719 (x : int) (y : int) : (term12 x y) = (term16 x y).
Proof. exact (TRANS (@lem2305715 x y) (@lem2305718 x y)). Qed.
Lemma lem2305720 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2305721 (x : int) (y : int) : (term4 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2305720) (@lem2305719 x y)). Qed.
Lemma lem2305723 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2305724 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (@lem2305723 (term19 x y)). Qed.
Lemma lem2305725 (x : int) (y : int) : (term4 x y) = (term18 x y).
Proof. exact (TRANS (@lem2305721 x y) (@lem2305724 x y)). Qed.
Lemma lem2305726 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term5 x y) = (term18 x y)).
Proof. exact (MK_COMB (@lem2305707 x y) (@lem2305725 x y)). Qed.
Lemma lem2305728 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305729 (x : int) (y : int) : ((term5 x y) = (term18 x y)) = ((int_min x y) = (term20 x y)).
Proof. exact (@lem2305728 (int_min x y) (term20 x y)). Qed.
Lemma lem2305730 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((int_min x y) = (term20 x y)).
Proof. exact (TRANS (@lem2305726 x y) (@lem2305729 x y)). Qed.
Lemma lem2305731 (x : int) (y : int) : (int_min x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2305730 x y) (@lem2305703 x y)). Qed.
Lemma lem2305732 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2305731 x y). Qed.
Lemma lem2305733 : term22.
Proof. exact (fun x : int => @lem2305732 x). Qed.
